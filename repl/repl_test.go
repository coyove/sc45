package repl

import (
	"net/http"
	"testing"

	"github.com/coyove/scmbed"
)

func TestLaunchWeb(t *testing.T) {
	it := scmbed.New()
	InjectDebugPProfREPL(it, "debug")
	http.ListenAndServe(":8080", nil)
}
