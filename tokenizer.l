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
S \"(\\.|[^"])*\"
L [A-Za-z]
ident {L}({L}|{D})*
contextedIdent ({ident}"`")*{ident}
blanks ___|__|_
pattern {blanks}|{contextedIdent}{blanks}|{blanks}{contextedIdent}|{contextedIdent}{blanks}{contextedIdent}

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

{S}
    tmps := string(y.buf)
    lval.val = &String{tmps[1:len(tmps)-1]}
    return STRING

\( return LPARSYM
\) return RPARSYM
, return COMMASYM
; return SEMISYM
\[ return LBRACKETSYM
\] return RBRACKETSYM
\{ return LCURLYSYM
\} return RCURLYSYM
-> return RULESYM
:> return RULEDELAYEDSYM
\+ return PLUSSYM
\- return MINUSSYM
\* return MULTSYM
\/ return DIVSYM
\^  return EXPSYM
= return SETSYM
:= return SETDELAYEDSYM
=== return SAMESYM
\/; return CONDITIONSYM
== return EQUALSYM
# return SLOTSYM
\/\. return REPLACEALLSYM
\/\/\. return REPLACEREPSYM
\/\/ return POSTFIXSYM
@ return FUNCAPPSYM
@@ return APPLYSYM
\/@ return MAPSYM
\? return PATTESTSYM

{pattern}
    delim := "_"
    blankType := &Symbol{"Blank"}
    if strings.Contains(string(y.buf), "___") {
        delim = "___"
        blankType = &Symbol{"BlankNullSequence"}
    } else if strings.Contains(string(y.buf), "__") {
        delim = "__"
        blankType = &Symbol{"BlankSequence"}
    }
    parts := strings.Split(string(y.buf), delim)
    if len(parts) == 1 {
        lval.val = &Expression{[]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, &Expression{[]Ex{blankType}}}}
        return PATTERN
    }
    if len(parts) == 2 {
        if parts[0] == "" {
            if parts[1] == "" {
                lval.val = &Expression{[]Ex{blankType}}
            } else {
                lval.val = &Expression{[]Ex{blankType, &Symbol{parts[1]}}}
            }
            return PATTERN
        } else {
            if parts[1] == "" {
                lval.val = &Expression{[]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, &Expression{[]Ex{blankType}}}}
            } else {
                lval.val = &Expression{[]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, &Expression{[]Ex{blankType, &Symbol{parts[1]}}}}}
            }
            return PATTERN
        }
    }
    lval.val = &Expression{[]Ex{&Symbol{"Error"}, &String{"Pattern parse error."}}}
    return PATTERN

{contextedIdent}
    lval.val = &Symbol{string(y.buf)}
    return NAME

%%
    y.empty = true
    return int(c)
}
