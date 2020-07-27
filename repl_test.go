package scmbed

import (
	"net/http"
	"os"
	"testing"
)

func TestLaunchWeb(t *testing.T) {
	if os.Getenv("WEB") != "" {
		it := New()
		it.InjectDebugPProfREPL("debug")
		http.ListenAndServe(":8080", nil)
	}
}
