%{
package main

import (
    "bufio"
    "log"
    "strconv"
    "github.com/corywalker/cas"
    "math/big"
)

type Calclexer struct{
    src     *bufio.Reader
    buf     []byte
    empty   bool
    current byte
}

func newLexer(src *bufio.Reader) (y *Calclexer) {
    y = &Calclexer{src: src}
    if b, err := src.ReadByte(); err == nil {
        y.current = b
    }
    return
}

func (y *Calclexer) getc() byte {
    if y.current != 0 {
        y.buf = append(y.buf, y.current)
    }
    y.current = 0
    if b, err := y.src.ReadByte(); err == nil {
        y.current = b
    }
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
E  [eE][-+]?{D}
F  {D}"."{D}?{E}?|{D}{E}?|"."{D}{E}?

%%
    y.buf = y.buf[:0]

[ \t\r]+

{F}
    var tmpf float64
    tmpf, err = strconv.ParseFloat(string(y.buf), 64)
    if err != nil {
        log.Fatal(err)
    }
    lval.val = &cas.Flt{big.NewFloat(tmpf)}

    return DIGIT

%%
    y.empty = true
    return int(c)
}
