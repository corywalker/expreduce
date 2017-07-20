%{
package expreduce

import (
    "log"
    "fmt"
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
    fmt.Printf("Syntax::sntx: %v.\n\n\n", e)
}

func (y *Calclexer) Lex(lval *CalcSymType) int {
    /*var err error*/
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
L [A-Za-z$]
ident {L}({L}|{D})*
contextedIdent ({ident}"`")*{ident}
blanks ___|__|_
dot "."
pattern {blanks}|{contextedIdent}{blanks}|{blanks}{contextedIdent}|{blanks}{dot}|{contextedIdent}{blanks}{contextedIdent}|{contextedIdent}{blanks}{dot}
comment         "(*"([^*\x80]|\*+[^*)\x80])*\*+\)

%%
    y.buf = y.buf[:0]

[ \t\r\n]+

{comment}

{D}
    var base int = 10
    tmpi := big.NewInt(0)
    _, ok := tmpi.SetString(string(y.buf), base)
    if !ok {
        log.Fatal("Failed in integer parsing.")
    }
    lval.val = &Integer{tmpi}

    return INTEGER

{F}
    tmpf := big.NewFloat(0)
    _, ok := tmpf.SetString(string(y.buf))
    if !ok {
        log.Fatal("Failed in float parsing.")
    }
    lval.val = &Flt{tmpf}

    return FLOAT

{S}
    tmps := string(y.buf)
    lval.val = &String{tmps[1:len(tmps)-1]}
    return STRING

\( return LPARSYM /* skipped */
\) return RPARSYM /* skipped */
, return COMMASYM /* skipped */
; return SEMISYM /* CompoundExpression */
;; return SPANSYM /* Span */
\[ return LBRACKETSYM /* skipped */
\] return RBRACKETSYM /* skipped */
\{ return LCURLYSYM /* skipped */
\} return RCURLYSYM /* skipped */
-> return RULESYM /* Rule */
:> return RULEDELAYEDSYM /* RuleDelayed */
\+ return PLUSSYM /* Plus */
\- return MINUSSYM /* */
\* return MULTSYM /* */
\/ return DIVSYM /* */
\^  return EXPSYM /* */
= return SETSYM /* set */
:= return SETDELAYEDSYM /* setdelayed */
=== return SAMESYM /* SameQ */
=!= return UNSAMESYM /* UnsameQ */
\/; return CONDITIONSYM /* Condition */
== return EQUALSYM /* Equal */
> return GREATERSYM /* Greater */
\< return LESSSYM /* Less */
\<\< return GETSYM /* Get */
>= return GREATEREQUALSYM /* GreaterEqual */
\<= return LESSEQUALSYM /* LessEqual */
\. return DOTSYM /* Dot, Optional */
\.\. return REPEATEDSYM /* Repeated */
\.\.\. return REPEATEDNULLSYM /* RepeatedNull */
! return EXCLAMATIONSYM /* Factorial, Not */
& return FUNCTIONSYM /* Factorial */
!= return UNEQUALSYM /* Unequal */
# return SLOTSYM /* Slot */
\/\. return REPLACEALLSYM /* ReplaceAll */
\/\/\. return REPLACEREPSYM /* ReplaceRepeated */
\/\/ return POSTFIXSYM /* */
@ return FUNCAPPSYM /* */
@@ return APPLYSYM /* */
\<> return STRINGJOINSYM /* StringJoin */
\/@ return MAPSYM /* Map */
\? return PATTESTSYM /* PatternTest */
\| return ALTSYM /* Alternatives */
: return COLONSYM /* Pattern */
\|\| return ORSYM /* Or */
&& return ANDSYM /* And */
:: return MESSAGENAMESYM /* MessageName */

{pattern}
    delim := "_"
    blankType := &Symbol{"System`Blank"}
    if strings.Contains(string(y.buf), "___") {
        delim = "___"
        blankType = &Symbol{"System`BlankNullSequence"}
    } else if strings.Contains(string(y.buf), "__") {
        delim = "__"
        blankType = &Symbol{"System`BlankSequence"}
    }
    parts := strings.Split(string(y.buf), delim)
    if len(parts) == 1 {
        lval.val = NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
        return PATTERN
    }
    if len(parts) == 2 {
        if parts[0] == "" {
            if parts[1] == "" {
                lval.val = NewExpression([]Ex{blankType})
            } else if delim == "_" && parts[1] == "." {
                lval.val = NewExpression([]Ex{&Symbol{"System`Optional"}, NewExpression([]Ex{blankType})})
            } else {
                lval.val = NewExpression([]Ex{blankType, &Symbol{parts[1]}})
            }
            return PATTERN
        } else {
            if parts[1] == "" {
                lval.val = NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
            } else if delim == "_" && parts[1] == "." {
                lval.val = NewExpression([]Ex{&Symbol{"System`Optional"}, NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})})
            } else {
                lval.val = NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType, &Symbol{parts[1]}})})
            }
            return PATTERN
        }
    }
    lval.val = NewExpression([]Ex{&Symbol{"System`Error"}, &String{"Pattern parse error."}})
    return PATTERN

{contextedIdent}
    lval.val = &Symbol{string(y.buf)}
    return NAME

%%
    y.empty = true
    return int(c)
}
