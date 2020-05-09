// +build linux darwin freebsd

package repl

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"os"
	"strings"
	"syscall"
	"unicode"

	"github.com/coyove/scmbed"
)

func RunSimplePipeREPL(it *scmbed.Interpreter, path string) error {
	os.Remove(path)
	if err := syscall.Mkfifo(path, 0777); err != nil {
		return err
	}

	text := bytes.Buffer{}
	text.WriteString(`
	rm -rf repl-ac || true
	touch2() { mkdir -p "$(dirname "$1")" && touch "$1" ; }
	`)

	for _, k := range it.Funcs() {
		name := strings.Split(k.String(), " ")[0]
		if len(name) == 0 || !unicode.IsLetter(rune(name[0])) {
			continue
		}
		text.WriteString(fmt.Sprintf("touch2 repl-ac/%s || true\n", name))
	}
	text.WriteString(fmt.Sprintf(`
cd repl-ac
while true; do
    read -p 'in > ' -e cmd
	history -s "$cmd"
    echo $cmd > %s && cat %s
done
`, path, path))

	if err := ioutil.WriteFile("repl", text.Bytes(), 0777); err != nil {
		return err
	}

	ww := &bytes.Buffer{}
	scmbed.DefaultStdout = ww

	for {
		f, err := os.Open(path)
		if err != nil {
			return err
		}
		tmp := [1024]byte{}
		n, _ := f.Read(tmp[:])
		f.Close()

		cmd := string(bytes.TrimSpace(tmp[:n]))

		ww.Reset()
		v, err := it.Run(cmd)

		resp := bytes.Buffer{}
		resp.WriteString("out > ")

		if ww.Len() > 0 {
			resp.Write(ww.Bytes())
		}

		if err != nil {
			resp.WriteString(err.Error())
		} else {
			resp.WriteString(fmt.Sprint(v))
		}
		resp.WriteRune('\n')

		if err := ioutil.WriteFile(path, resp.Bytes(), 0777); err != nil {
			return err
		}
	}
}
