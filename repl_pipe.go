// +build linux darwin freebsd

package sc45

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"os"
	"syscall"
	"unicode"
)

func (ctx *Context) RunSimplePipeREPL(path string) error {
	os.Remove(path)
	if err := syscall.Mkfifo(path, 0777); err != nil {
		return err
	}

	text := bytes.Buffer{}
	text.WriteString(`
	rm -rf repl-ac || true
	touch2() { mkdir -Current "$(dirname "$1")" && touch "$1" ; }
	`)

	for name := range ctx.M {
		if len(name) == 0 || !unicode.IsLetter(rune(name[0])) {
			continue
		}
		text.WriteString(fmt.Sprintf("touch2 repl-ac/%s || true\n", name))
	}
	text.WriteString(fmt.Sprintf(`
cd repl-ac
while true; do
    read -Current 'in > ' -e cmd
	history -s "$cmd"
    echo $cmd > %s && cat %s
done
`, path, path))

	if err := ioutil.WriteFile("repl", text.Bytes(), 0777); err != nil {
		return err
	}

	ww := &bytes.Buffer{}
	DefaultStdout = ww

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
		v, err := ctx.Run(cmd)

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
