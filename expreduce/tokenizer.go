// CAUTION: Generated file - DO NOT EDIT.

package expreduce

import (
	"fmt"
	"log"
	"math/big"
	"strings"
)

type Calclexer struct {
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

	/*E  [eE][-+]?{D}*/
	/*F  {D}"."{D}?{E}?|{D}{E}?|"."{D}{E}?*/

yystate0:

	y.buf = y.buf[:0]

	goto yystart1

	goto yystate0 // silence unused label error
	goto yystate1 // silence unused label error
yystate1:
	c = y.getc()
yystart1:
	switch {
	default:
		goto yyabort
	case c == '!':
		goto yystate3
	case c == '"':
		goto yystate5
	case c == '#':
		goto yystate9
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate10
	case c == '&':
		goto yystate18
	case c == '(':
		goto yystate20
	case c == ')':
		goto yystate24
	case c == '*':
		goto yystate25
	case c == '+':
		goto yystate26
	case c == ',':
		goto yystate27
	case c == '-':
		goto yystate28
	case c == '.':
		goto yystate30
	case c == '/':
		goto yystate34
	case c == ':':
		goto yystate41
	case c == ';':
		goto yystate45
	case c == '<':
		goto yystate47
	case c == '=':
		goto yystate51
	case c == '>':
		goto yystate56
	case c == '?':
		goto yystate58
	case c == '@':
		goto yystate59
	case c == '[':
		goto yystate61
	case c == '\t' || c == '\n' || c == '\r' || c == ' ':
		goto yystate2
	case c == ']':
		goto yystate62
	case c == '^':
		goto yystate63
	case c == '_':
		goto yystate11
	case c == '{':
		goto yystate64
	case c == '|':
		goto yystate65
	case c == '}':
		goto yystate67
	case c >= '0' && c <= '9':
		goto yystate40
	}

yystate2:
	c = y.getc()
	switch {
	default:
		goto yyrule1
	case c == '\t' || c == '\n' || c == '\r' || c == ' ':
		goto yystate2
	}

yystate3:
	c = y.getc()
	switch {
	default:
		goto yyrule36
	case c == '=':
		goto yystate4
	}

yystate4:
	c = y.getc()
	goto yyrule38

yystate5:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '"':
		goto yystate6
	case c == '\\':
		goto yystate7
	case c >= '\x01' && c <= '!' || c >= '#' && c <= '[' || c >= ']' && c <= 'ÿ':
		goto yystate5
	}

yystate6:
	c = y.getc()
	goto yyrule5

yystate7:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '"':
		goto yystate8
	case c == '\\':
		goto yystate7
	case c >= '\x01' && c <= '!' || c >= '#' && c <= '[' || c >= ']' && c <= 'ÿ':
		goto yystate5
	}

yystate8:
	c = y.getc()
	switch {
	default:
		goto yyrule5
	case c == '"':
		goto yystate6
	case c == '\\':
		goto yystate7
	case c >= '\x01' && c <= '!' || c >= '#' && c <= '[' || c >= ']' && c <= 'ÿ':
		goto yystate5
	}

yystate9:
	c = y.getc()
	goto yyrule39

yystate10:
	c = y.getc()
	switch {
	default:
		goto yyrule54
	case c == '$' || c >= '0' && c <= '9' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate10
	case c == '_':
		goto yystate11
	case c == '`':
		goto yystate17
	}

yystate11:
	c = y.getc()
	switch {
	default:
		goto yyrule53
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate12
	case c == '.':
		goto yystate14
	case c == '_':
		goto yystate15
	}

yystate12:
	c = y.getc()
	switch {
	default:
		goto yyrule53
	case c == '$' || c >= '0' && c <= '9' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate12
	case c == '`':
		goto yystate13
	}

yystate13:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate12
	}

yystate14:
	c = y.getc()
	goto yyrule53

yystate15:
	c = y.getc()
	switch {
	default:
		goto yyrule53
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate12
	case c == '.':
		goto yystate14
	case c == '_':
		goto yystate16
	}

yystate16:
	c = y.getc()
	switch {
	default:
		goto yyrule53
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate12
	case c == '.':
		goto yystate14
	}

yystate17:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '$' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z':
		goto yystate10
	}

yystate18:
	c = y.getc()
	switch {
	default:
		goto yyrule37
	case c == '&':
		goto yystate19
	}

yystate19:
	c = y.getc()
	goto yyrule51

yystate20:
	c = y.getc()
	switch {
	default:
		goto yyrule6
	case c == '*':
		goto yystate21
	}

yystate21:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '*':
		goto yystate22
	case c >= '\x01' && c <= ')' || c >= '+' && c <= '\u007f' || c >= '\u0081' && c <= 'ÿ':
		goto yystate21
	}

yystate22:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == ')':
		goto yystate23
	case c == '*':
		goto yystate22
	case c >= '\x01' && c <= '(' || c >= '+' && c <= '\u007f' || c >= '\u0081' && c <= 'ÿ':
		goto yystate21
	}

yystate23:
	c = y.getc()
	goto yyrule2

yystate24:
	c = y.getc()
	goto yyrule7

yystate25:
	c = y.getc()
	goto yyrule19

yystate26:
	c = y.getc()
	goto yyrule17

yystate27:
	c = y.getc()
	goto yyrule8

yystate28:
	c = y.getc()
	switch {
	default:
		goto yyrule18
	case c == '>':
		goto yystate29
	}

yystate29:
	c = y.getc()
	goto yyrule15

yystate30:
	c = y.getc()
	switch {
	default:
		goto yyrule33
	case c == '.':
		goto yystate31
	case c >= '0' && c <= '9':
		goto yystate33
	}

yystate31:
	c = y.getc()
	switch {
	default:
		goto yyrule34
	case c == '.':
		goto yystate32
	}

yystate32:
	c = y.getc()
	goto yyrule35

yystate33:
	c = y.getc()
	switch {
	default:
		goto yyrule4
	case c >= '0' && c <= '9':
		goto yystate33
	}

yystate34:
	c = y.getc()
	switch {
	default:
		goto yyrule20
	case c == '.':
		goto yystate35
	case c == '/':
		goto yystate36
	case c == ';':
		goto yystate38
	case c == '@':
		goto yystate39
	}

yystate35:
	c = y.getc()
	goto yyrule40

yystate36:
	c = y.getc()
	switch {
	default:
		goto yyrule42
	case c == '.':
		goto yystate37
	}

yystate37:
	c = y.getc()
	goto yyrule41

yystate38:
	c = y.getc()
	goto yyrule26

yystate39:
	c = y.getc()
	goto yyrule46

yystate40:
	c = y.getc()
	switch {
	default:
		goto yyrule3
	case c == '.':
		goto yystate33
	case c >= '0' && c <= '9':
		goto yystate40
	}

yystate41:
	c = y.getc()
	switch {
	default:
		goto yyrule49
	case c == ':':
		goto yystate42
	case c == '=':
		goto yystate43
	case c == '>':
		goto yystate44
	}

yystate42:
	c = y.getc()
	goto yyrule52

yystate43:
	c = y.getc()
	goto yyrule23

yystate44:
	c = y.getc()
	goto yyrule16

yystate45:
	c = y.getc()
	switch {
	default:
		goto yyrule9
	case c == ';':
		goto yystate46
	}

yystate46:
	c = y.getc()
	goto yyrule10

yystate47:
	c = y.getc()
	switch {
	default:
		goto yyrule29
	case c == '<':
		goto yystate48
	case c == '=':
		goto yystate49
	case c == '>':
		goto yystate50
	}

yystate48:
	c = y.getc()
	goto yyrule30

yystate49:
	c = y.getc()
	goto yyrule32

yystate50:
	c = y.getc()
	goto yyrule45

yystate51:
	c = y.getc()
	switch {
	default:
		goto yyrule22
	case c == '!':
		goto yystate52
	case c == '=':
		goto yystate54
	}

yystate52:
	c = y.getc()
	switch {
	default:
		goto yyabort
	case c == '=':
		goto yystate53
	}

yystate53:
	c = y.getc()
	goto yyrule25

yystate54:
	c = y.getc()
	switch {
	default:
		goto yyrule27
	case c == '=':
		goto yystate55
	}

yystate55:
	c = y.getc()
	goto yyrule24

yystate56:
	c = y.getc()
	switch {
	default:
		goto yyrule28
	case c == '=':
		goto yystate57
	}

yystate57:
	c = y.getc()
	goto yyrule31

yystate58:
	c = y.getc()
	goto yyrule47

yystate59:
	c = y.getc()
	switch {
	default:
		goto yyrule43
	case c == '@':
		goto yystate60
	}

yystate60:
	c = y.getc()
	goto yyrule44

yystate61:
	c = y.getc()
	goto yyrule11

yystate62:
	c = y.getc()
	goto yyrule12

yystate63:
	c = y.getc()
	goto yyrule21

yystate64:
	c = y.getc()
	goto yyrule13

yystate65:
	c = y.getc()
	switch {
	default:
		goto yyrule48
	case c == '|':
		goto yystate66
	}

yystate66:
	c = y.getc()
	goto yyrule50

yystate67:
	c = y.getc()
	goto yyrule14

yyrule1: // [ \t\r\n]+

	goto yystate0
yyrule2: // {comment}

	goto yystate0
yyrule3: // {D}
	{

		var base int = 10
		tmpi := big.NewInt(0)
		_, ok := tmpi.SetString(string(y.buf), base)
		if !ok {
			log.Fatal("Failed in integer parsing.")
		}
		lval.val = &Integer{tmpi}
		return INTEGER
	}
yyrule4: // {F}
	{

		tmpf := big.NewFloat(0)
		_, ok := tmpf.SetString(string(y.buf))
		if !ok {
			log.Fatal("Failed in float parsing.")
		}
		lval.val = &Flt{tmpf}
		return FLOAT
	}
yyrule5: // {S}
	{

		tmps := string(y.buf)
		tmps = tmps[1 : len(tmps)-1]
		// Handle some escape characters
		tmps = strings.Replace(tmps, "\\\"", "\"", -1)
		tmps = strings.Replace(tmps, "\\n", "\n", -1)
		tmps = strings.Replace(tmps, "\\t", "\t", -1)
		lval.val = &String{tmps}
		return STRING
	}
yyrule6: // \(
	{
		return LPARSYM /* skipped */
	}
yyrule7: // \)
	{
		return RPARSYM /* skipped */
	}
yyrule8: // ,
	{
		return COMMASYM /* skipped */
	}
yyrule9: // ;
	{
		return SEMISYM /* CompoundExpression */
	}
yyrule10: // ;;
	{
		return SPANSYM /* Span */
	}
yyrule11: // \[
	{
		return LBRACKETSYM /* skipped */
	}
yyrule12: // \]
	{
		return RBRACKETSYM /* skipped */
	}
yyrule13: // \{
	{
		return LCURLYSYM /* skipped */
	}
yyrule14: // \}
	{
		return RCURLYSYM /* skipped */
	}
yyrule15: // ->
	{
		return RULESYM /* Rule */
	}
yyrule16: // :>
	{
		return RULEDELAYEDSYM /* RuleDelayed */
	}
yyrule17: // \+
	{
		return PLUSSYM /* Plus */
	}
yyrule18: // \-
	{
		return MINUSSYM /* */
	}
yyrule19: // \*
	{
		return MULTSYM /* */
	}
yyrule20: // \/
	{
		return DIVSYM /* */
	}
yyrule21: // \^
	{
		return EXPSYM /* */
	}
yyrule22: // =
	{
		return SETSYM /* set */
	}
yyrule23: // :=
	{
		return SETDELAYEDSYM /* setdelayed */
	}
yyrule24: // ===
	{
		return SAMESYM /* SameQ */
	}
yyrule25: // =!=
	{
		return UNSAMESYM /* UnsameQ */
	}
yyrule26: // \/;
	{
		return CONDITIONSYM /* Condition */
	}
yyrule27: // ==
	{
		return EQUALSYM /* Equal */
	}
yyrule28: // >
	{
		return GREATERSYM /* Greater */
	}
yyrule29: // \<
	{
		return LESSSYM /* Less */
	}
yyrule30: // \<\<
	{
		return GETSYM /* Get */
	}
yyrule31: // >=
	{
		return GREATEREQUALSYM /* GreaterEqual */
	}
yyrule32: // \<=
	{
		return LESSEQUALSYM /* LessEqual */
	}
yyrule33: // \.
	{
		return DOTSYM /* Dot, Optional */
	}
yyrule34: // \.\.
	{
		return REPEATEDSYM /* Repeated */
	}
yyrule35: // \.\.\.
	{
		return REPEATEDNULLSYM /* RepeatedNull */
	}
yyrule36: // !
	{
		return EXCLAMATIONSYM /* Factorial, Not */
	}
yyrule37: // &
	{
		return FUNCTIONSYM /* Factorial */
	}
yyrule38: // !=
	{
		return UNEQUALSYM /* Unequal */
	}
yyrule39: // #
	{
		return SLOTSYM /* Slot */
	}
yyrule40: // \/\.
	{
		return REPLACEALLSYM /* ReplaceAll */
	}
yyrule41: // \/\/\.
	{
		return REPLACEREPSYM /* ReplaceRepeated */
	}
yyrule42: // \/\/
	{
		return POSTFIXSYM /* */
	}
yyrule43: // @
	{
		return FUNCAPPSYM /* */
	}
yyrule44: // @@
	{
		return APPLYSYM /* */
	}
yyrule45: // \<>
	{
		return STRINGJOINSYM /* StringJoin */
	}
yyrule46: // \/@
	{
		return MAPSYM /* Map */
	}
yyrule47: // \?
	{
		return PATTESTSYM /* PatternTest */
	}
yyrule48: // \|
	{
		return ALTSYM /* Alternatives */
	}
yyrule49: // :
	{
		return COLONSYM /* Pattern */
	}
yyrule50: // \|\|
	{
		return ORSYM /* Or */
	}
yyrule51: // &&
	{
		return ANDSYM /* And */
	}
yyrule52: // ::
	{
		return MESSAGENAMESYM /* MessageName */
	}
yyrule53: // {pattern}
	{

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
	}
yyrule54: // {contextedIdent}
	{

		lval.val = &Symbol{string(y.buf)}
		return NAME
	}
	panic("unreachable")

	goto yyabort // silence unused label error

yyabort: // no lexem recognized
	y.empty = true
	return int(c)
}
