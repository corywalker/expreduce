%{
package main

import (
    "log"
    "strconv"
    "github.com/corywalker/cas"
    "math/big"
)

type Calclexer struct{
    s       string
    pos     int
    buf     []rune
    empty   bool
    current rune
}

func newLexer(s string) (y *Calclexer) {
    y = &Calclexer{s: s}
    if y.pos != len(y.s) {
        y.current = rune(y.s[y.pos])
    }
    /*fmt.Printf("y.current: %d, y.pos: %d, '%s'\n", y.current, y.pos, y.buf)*/
    y.pos += 1
    return
}

func (y *Calclexer) getc() rune {
    if y.current != 0 {
        y.buf = append(y.buf, y.current)
    }
    y.current = 0
    if y.pos != len(y.s) {
        y.current = rune(y.s[y.pos])
    }
    /*fmt.Printf("y.current: %d, y.pos: %d, '%s'\n", y.current, y.pos, y.buf)*/
    y.pos += 1
    return y.current
}

func (y Calclexer) Error(e string) {
    log.Fatal(e)
}

func (y *Calclexer) Lex(lval *CalcSymType) int {
    var err error
    c := y.current
    if y.empty {
        c, y.empty = y.getc(), false
    }
%}

%yyc c
%yyn c = y.getc()

D  [0-9]+
/*E  [eE][-+]?{D}*/
/*F  {D}"."{D}?{E}?|{D}{E}?|"."{D}{E}?*/
F  {D}"."{D}?|"."{D}|{D}

%%
    y.buf = y.buf[:0]

[ \t\r]+

{D}
    var tmpf float64
    tmpf, err = strconv.ParseFloat(string(y.buf), 64)
    if err != nil {
        log.Fatal(err)
    }
    lval.val = &cas.Flt{big.NewFloat(tmpf)}

    return INTEGER

{F}
    var tmpf float64
    tmpf, err = strconv.ParseFloat(string(y.buf), 64)
    if err != nil {
        log.Fatal(err)
    }
    lval.val = &cas.Flt{big.NewFloat(tmpf)}

    return FLOAT

%%
    y.empty = true
    return int(c)
}
