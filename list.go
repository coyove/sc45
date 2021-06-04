package sc45

import (
	"fmt"
	"strings"
)

type Pair struct {
	next  *Pair
	val   Value
	empty bool
}

type ListBuilder struct {
	Len             int
	head, last, Cur *Pair
}

func (p *Pair) Car() Value {
	panicif(p.Empty(), "car: empty list")
	return p.val
}

func (p *Pair) SetCar(v Value) *Pair {
	panicif(p.Empty(), "car: empty list")
	p.val = v
	return p
}

func (p *Pair) Cdr() (v Value) {
	p = p.next
	panicif(p == nil, "cdr: empty list")
	return v.nop(p.Improper() && v.Set(p.val) || v.Set(List(p)))
}

func (p *Pair) SetCdr(v Value) *Pair {
	panicif(p.Empty(), "cdr: empty list")
	if v.Type() == ListType {
		p.next = v.List()
	} else {
		p.next = &Pair{val: v}
	}
	return p
}

func (p *Pair) Improper() bool {
	return p.next == nil && !p.empty
}

func (p *Pair) Empty() bool {
	return p.next == nil && p.empty
}

func (p *Pair) MustProper() *Pair {
	panicif(p.Improper(), "improper list")
	return p
}

func (p *Pair) ProperCdr() bool {
	return p.next != nil && !p.next.MustProper().Empty()
}

func (p *Pair) Length() (length int) {
	for ; !p.MustProper().Empty(); p = p.next {
		length++
	}
	return
}

func (p *Pair) Foreach(cb func(Value) bool) {
	for flag := true; flag && !p.MustProper().Empty(); p = p.next {
		flag = cb(p.val)
	}
}

func (p *Pair) ToSlice() (s []Value) {
	p.Foreach(func(v Value) bool { s = append(s, v); return true })
	return
}

func (p *Pair) match(state execState, pattern *Pair, metWildcard bool, symbols map[string]struct{}, m map[string]Value) bool {
	if pattern.MustProper().Empty() {
		return p.MustProper().Empty()
	}
	isWildcard := func(s string) string {
		if strings.HasSuffix(s, "*") {
			panicif(metWildcard, "multiple wildcards in one pattern")
			return ifstr(len(s) == 1, "*", s[:len(s)-1])
		}
		return ""
	}
	if p.MustProper().Empty() {
		if pattern.val.Type() == SymType && !pattern.ProperCdr() {
			if w := isWildcard(pattern.val.Str()); w != "" {
				m[w] = List(Empty)
				return true
			}
		}
		return false
	}
	switch pattern.val.Type() {
	case SymType:
		sym := pattern.val.Str()
		if sym == "_" {
			break
		}
		if _, ok := symbols[sym]; ok {
			if !pattern.val.Equals(p.val) {
				return false
			}
			break
		}
		if w := isWildcard(sym); w != "" {
			if pattern.ProperCdr() {
				n := p.Length() - pattern.next.Length()
				if n < 0 { // the remaining symbols in 'p' is less than 'pattern', so we are sure the match will fail
					return false
				}
				// The first n symbols will go into 'ww'
				ww := InitListBuilder()
				for ; n > 0; n-- {
					ww = ww.Append(p.val)
					p = p.next
				}
				m[w] = ww.Build()
				return p.match(state, pattern.next, true, symbols, m)
			}
			m[w] = List(p)
			return true
		}
		if strings.HasPrefix(sym, "#:") {
			if !p.val.Equals(pattern.val) {
				return false
			}
			break
		}
		m[sym] = p.val
	case ListType:
		if lst := pattern.val.List(); lst.val.Type() == SymType && lst.val.Str() == "quote" {
			if __exec(lst.next.val, execState{
				deadline: state.deadline,
				debug:    state.debug,
				local:    &Context{parent: state.local, M: map[string]Value{"_": p.val}},
			}).Falsy() {
				return false
			}
			m["_"] = p.val
			break
		}
		if p.val.Type() != ListType {
			return false
		}
		if !p.val.List().match(state, pattern.val.List(), false, symbols, m) {
			return false
		}
	default:
		if !p.val.Equals(pattern.val) {
			return false
		}
	}
	return p.next.match(state, pattern.next, false, symbols, m)
}

// Take takes n values from the list, -1 means all values, -2 means all but the last value
func (p *Pair) Take(n int) *Pair {
	b := InitListBuilder()
	for ; p != nil && !p.Empty() && (b.Len < n || n < 0); p = p.next {
		b = b.Append(p.val)
	}
	if n == -2 {
		panicif(b.last == nil, "take(-2): empty list")
		*b.last = *Empty
	} else if n == -1 { // take all, do nothing
	} else if b.Len != n {
		panic(fmt.Errorf("take(%d): not enough values (%d)", n, b.Len))
	}
	return b.head
}

func (p *Pair) Last() (last *Pair) {
	for ; p != nil && !p.Empty(); p = p.next {
		last = p
	}
	return
}

func (p *Pair) Proper() bool {
	for ; ; p = p.next {
		if p.Improper() || p.Empty() {
			return p.Empty()
		}
	}
}

func moveCdr(ll **Pair) bool {
	if (*ll).ProperCdr() {
		*ll = (*ll).next
		return true
	}
	*ll = Empty
	return false
}

func Cons(v, v2 Value) *Pair {
	return (&Pair{val: v}).SetCdr(v2)
}

func InitListBuilder() (b ListBuilder) {
	b.Cur = &Pair{empty: true}
	b.head = b.Cur
	return b
}

func (b ListBuilder) Build() Value {
	return List(b.head)
}

func (b ListBuilder) Append(v Value) ListBuilder {
	panicif(!b.Cur.empty, "append to improper list")
	b.Cur.val, b.Cur.next, b.Cur.empty = v, &Pair{empty: true}, false
	b.last = b.Cur
	b.Cur, b.Len = b.Cur.next, b.Len+1
	return b
}
