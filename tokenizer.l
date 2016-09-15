%{
package cas

import (
    "log"
    "strconv"
    "math/big"
    "strings"
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
L [A-Za-z]
ident {L}({L}|{D})*
blanks ___|__|_
pattern {blanks}|{ident}{blanks}|{blanks}{ident}|{ident}{blanks}{ident}

%%
    y.buf = y.buf[:0]

[ \t\r]+

{D}
    var tmpi int64
    var base int = 10
    tmpi, err = strconv.ParseInt(string(y.buf), base, 64)
    if err != nil {
        log.Fatal(err)
    }
    lval.val = &Integer{big.NewInt(tmpi)}

    return INTEGER

{F}
    var tmpf float64
    tmpf, err = strconv.ParseFloat(string(y.buf), 64)
    if err != nil {
        log.Fatal(err)
    }
    lval.val = &Flt{big.NewFloat(tmpf)}

    return FLOAT

\( return LPARSYM
\) return RPARSYM
, return COMMASYM
\[ return LBRACKETSYM
\] return RBRACKETSYM
-> return RULESYM
\+ return PLUSSYM
\- return MINUSSYM
\* return MULTSYM
\/ return DIVSYM
\^  return EXPSYM
= return SETSYM
:= return SETDELAYEDSYM
=== return SAMESYM
== return EQUALSYM
\/\. return REPLACESYM
\/\/\. return REPLACEREPSYM

{pattern}
    delim := "_"
    if strings.Contains(string(y.buf), "___") {
        delim = "___"
    } else if strings.Contains(string(y.buf), "__") {
        delim = "__"
    }
    parts := strings.Split(string(y.buf), delim)
    if len(parts) == 1 {
        if delim == "___" {
            lval.val = &Pattern{&Symbol{parts[0]}, &BlankNullSequence{}}
        } else if delim == "__" {
            lval.val = &Pattern{&Symbol{parts[0]}, &BlankSequence{}}
        } else {
            lval.val = &Pattern{&Symbol{parts[0]}, &Blank{}}
        }
        return PATTERN
    }
    if len(parts) == 2 {
        if parts[0] == "" {
            if delim == "___" {
                lval.val = &BlankNullSequence{&Symbol{parts[1]}}
            } else if delim == "__" {
                lval.val = &BlankSequence{&Symbol{parts[1]}}
            } else {
                lval.val = &Blank{&Symbol{parts[1]}}
            }
            return PATTERN
        } else {
            if delim == "___" {
                lval.val = &Pattern{&Symbol{parts[0]}, &BlankNullSequence{&Symbol{parts[1]}}}
            } else if delim == "__" {
                lval.val = &Pattern{&Symbol{parts[0]}, &BlankSequence{&Symbol{parts[1]}}}
            } else {
                lval.val = &Pattern{&Symbol{parts[0]}, &Blank{&Symbol{parts[1]}}}
            }
            return PATTERN
        }
    }
    lval.val = &Error{"Pattern parse error."}
    return PATTERN

{ident}
    lval.val = &Symbol{string(y.buf)}
    return NAME

%%
    y.empty = true
    return int(c)
}
