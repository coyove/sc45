package sc45

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net/http"
	"net/url"
	"strconv"
	"strings"
	"time"
)

type respStruct struct {
	Result string
	Stdout string
}

func (ctx *Context) InjectDebugPProfREPL(title string) {

	ww := &bytes.Buffer{}
	DefaultStdout = ww

	http.HandleFunc("/debug/pprof/repl", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == "GET" {
			p := bytes.Buffer{}
			p.WriteString(`<!doctype html><html><meta charset="UTF-8"><title>REPL: ` + title + `</title>
<style>
	body { font-size: 16px }
	* {box-sizing: border-box; font-family: monospace;}
	a {text-decoration: none}
	.results div:nth-child(even) {background: #eee}
	.results > div { display: block !important; clear:both }
	.results .result {margin-left:1em;white-space:pre-wrap;float:right}
</style>
<script src="https://cdn.jsdelivr.net/gh/coyove/sc45/tribute.min.js" ></script>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/tributejs/5.1.2/tribute.min.css" integrity="sha256-jCuf8eDAzmPpRqt5n0v1utTOCeWZc4OrGbv24Pw+ltk=" crossorigin="anonymous" />

<form onsubmit="var _=this;post('',{cmd:this.querySelector('#cmd').value},function(obj, data){
	var el = _.nextElementSibling.nextElementSibling.cloneNode(true);
	el.querySelector('.options').innerText = data.cmd;
	el.querySelector('.options').onclick = function() { document.getElementById('cmd').value = data.cmd }
	el.querySelector('.result').innerText = obj.Result;
	if (obj.Stdout) el.querySelector('.result').innerHTML += '\n<b>Stdout:</b>\n' + obj.Stdout;
	_.nextElementSibling.insertBefore(el,_.nextElementSibling.firstChild)
});return false;">
<input id=cmd style="width:100%;padding:0.5em;margin:0.5em 0;font-size:16px" placeholder="Commands ...">
<input type=submit style="display:none">
</form>
<div class=results></div>
<div style='display:none'> <a href='#' class=options></a><span class=result>z</span></div>

<script>
(new Tribute({
	collection: [{
		trigger: '(',
		lookup: 'key',
		values: function (text, cb) {
			post("?all=1", {}, function(results) {
				cb(results.filter(function(r) { return r.key.indexOf(text) > -1 }));
			})
		},
		selectTemplate: function (item) { return '(' + item.original.key },
		menuItemTemplate: function (item) { return item.original.doc; },
		replaceTextSuffix: '\n',
		positionMenu: true,
	}]
})).attach(document.getElementById('cmd'))

function post(url, data, cb) {
    var xml = new XMLHttpRequest(), q = "";
	xml.onreadystatechange = function() {
		if (xml.readyState == 4 && xml.status == 200) cb(JSON.parse(xml.responseText), data) 
	}
	xml.open("POST", url, true);
	xml.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
	for (var k in data) if (data.hasOwnProperty(k)) q += '&' + k + '=' + encodeURIComponent(data[k]);
	xml.send(q);
}
</script>
`)
			w.Header().Add("Content-Type", "text/html")
			w.Write(p.Bytes())
			return
		}

		if r.FormValue("all") != "" {
			keys := []map[string]string{}
			for k := range ctx.M {
				keys = append(keys, map[string]string{"key": k, "doc": k})
			}
			buf, _ := json.Marshal(keys)
			w.Write(buf)
			return
		}

		cmd := r.FormValue("cmd")
		timeout, _ := strconv.ParseInt(r.FormValue("timeout"), 10, 64)
		deadline := Forever
		if timeout != 0 {
			deadline = time.Now().Add(time.Duration(timeout) * time.Second)
		}

		ww.Reset()
		v, err := ctx.Run(deadline, cmd)

		var resp = respStruct{
			Stdout: ww.String(),
			Result: fmt.Sprint(v),
		}
		if err != nil {
			resp.Result = err.Error()
		}

		p, _ := json.Marshal(resp)
		w.Header().Add("Content-Type", "application/json")
		w.Write([]byte(p))
	})
}

func CallHTTPRepl(c *http.Client, addr, expr string) (result, stdout string, err error) {
	addr = strings.TrimPrefix(addr, "http://")
	addr = strings.TrimSuffix(addr, "/")

	resp, err := c.Post("http://"+addr+"/debug/pprof/repl",
		"application/x-www-form-urlencoded",
		strings.NewReader(`cmd=`+url.QueryEscape(expr)))
	if err != nil {
		return "", "", err
	}

	p, _ := ioutil.ReadAll(resp.Body)
	resp.Body.Close()
	s := respStruct{}
	json.Unmarshal(p, &s)
	return s.Result, s.Stdout, nil
}
