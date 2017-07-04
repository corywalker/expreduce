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
		goto yystate54
	case c == '?':
		goto yystate56
	case c == '@':
		goto yystate57
	case c == '[':
		goto yystate59
	case c == '\t' || c == '\n' || c == '\r' || c == ' ':
		goto yystate2
	case c == ']':
		goto yystate60
	case c == '^':
		goto yystate61
	case c == '_':
		goto yystate11
	case c == '{':
		goto yystate62
	case c == '|':
		goto yystate63
	case c == '}':
		goto yystate65
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
		goto yyrule35
	case c == '=':
		goto yystate4
	}

yystate4:
	c = y.getc()
	goto yyrule37

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
	goto yyrule38

yystate10:
	c = y.getc()
	switch {
	default:
		goto yyrule53
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
		goto yyrule52
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
		goto yyrule52
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
	goto yyrule52

yystate15:
	c = y.getc()
	switch {
	default:
		goto yyrule52
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
		goto yyrule52
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
		goto yyrule36
	case c == '&':
		goto yystate19
	}

yystate19:
	c = y.getc()
	goto yyrule50

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
		goto yyrule32
	case c == '.':
		goto yystate31
	case c >= '0' && c <= '9':
		goto yystate33
	}

yystate31:
	c = y.getc()
	switch {
	default:
		goto yyrule33
	case c == '.':
		goto yystate32
	}

yystate32:
	c = y.getc()
	goto yyrule34

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
	goto yyrule39

yystate36:
	c = y.getc()
	switch {
	default:
		goto yyrule41
	case c == '.':
		goto yystate37
	}

yystate37:
	c = y.getc()
	goto yyrule40

yystate38:
	c = y.getc()
	goto yyrule25

yystate39:
	c = y.getc()
	goto yyrule45

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
		goto yyrule48
	case c == ':':
		goto yystate42
	case c == '=':
		goto yystate43
	case c == '>':
		goto yystate44
	}

yystate42:
	c = y.getc()
	goto yyrule51

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
		goto yyrule28
	case c == '<':
		goto yystate48
	case c == '=':
		goto yystate49
	case c == '>':
		goto yystate50
	}

yystate48:
	c = y.getc()
	goto yyrule29

yystate49:
	c = y.getc()
	goto yyrule31

yystate50:
	c = y.getc()
	goto yyrule44

yystate51:
	c = y.getc()
	switch {
	default:
		goto yyrule22
	case c == '=':
		goto yystate52
	}

yystate52:
	c = y.getc()
	switch {
	default:
		goto yyrule26
	case c == '=':
		goto yystate53
	}

yystate53:
	c = y.getc()
	goto yyrule24

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
	goto yyrule30

yystate56:
	c = y.getc()
	goto yyrule46

yystate57:
	c = y.getc()
	switch {
	default:
		goto yyrule42
	case c == '@':
		goto yystate58
	}

yystate58:
	c = y.getc()
	goto yyrule43

yystate59:
	c = y.getc()
	goto yyrule11

yystate60:
	c = y.getc()
	goto yyrule12

yystate61:
	c = y.getc()
	goto yyrule21

yystate62:
	c = y.getc()
	goto yyrule13

yystate63:
	c = y.getc()
	switch {
	default:
		goto yyrule47
	case c == '|':
		goto yystate64
	}

yystate64:
	c = y.getc()
	goto yyrule49

yystate65:
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
		lval.val = &String{tmps[1 : len(tmps)-1]}
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
yyrule25: // \/;
	{
		return CONDITIONSYM /* Condition */
	}
yyrule26: // ==
	{
		return EQUALSYM /* Equal */
	}
yyrule27: // >
	{
		return GREATERSYM /* Greater */
	}
yyrule28: // \<
	{
		return LESSSYM /* Less */
	}
yyrule29: // \<\<
	{
		return GETSYM /* Get */
	}
yyrule30: // >=
	{
		return GREATEREQUALSYM /* GreaterEqual */
	}
yyrule31: // \<=
	{
		return LESSEQUALSYM /* LessEqual */
	}
yyrule32: // \.
	{
		return DOTSYM /* Dot, Optional */
	}
yyrule33: // \.\.
	{
		return REPEATEDSYM /* Repeated */
	}
yyrule34: // \.\.\.
	{
		return REPEATEDNULLSYM /* RepeatedNull */
	}
yyrule35: // !
	{
		return EXCLAMATIONSYM /* Factorial, Not */
	}
yyrule36: // &
	{
		return FUNCTIONSYM /* Factorial */
	}
yyrule37: // !=
	{
		return UNEQUALSYM /* Unequal */
	}
yyrule38: // #
	{
		return SLOTSYM /* Slot */
	}
yyrule39: // \/\.
	{
		return REPLACEALLSYM /* ReplaceAll */
	}
yyrule40: // \/\/\.
	{
		return REPLACEREPSYM /* ReplaceRepeated */
	}
yyrule41: // \/\/
	{
		return POSTFIXSYM /* */
	}
yyrule42: // @
	{
		return FUNCAPPSYM /* */
	}
yyrule43: // @@
	{
		return APPLYSYM /* */
	}
yyrule44: // \<>
	{
		return STRINGJOINSYM /* StringJoin */
	}
yyrule45: // \/@
	{
		return MAPSYM /* Map */
	}
yyrule46: // \?
	{
		return PATTESTSYM /* PatternTest */
	}
yyrule47: // \|
	{
		return ALTSYM /* Alternatives */
	}
yyrule48: // :
	{
		return COLONSYM /* Pattern */
	}
yyrule49: // \|\|
	{
		return ORSYM /* Or */
	}
yyrule50: // &&
	{
		return ANDSYM /* And */
	}
yyrule51: // ::
	{
		return MESSAGENAMESYM /* MessageName */
	}
yyrule52: // {pattern}
	{

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
			lval.val = NewExpression([]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
			return PATTERN
		}
		if len(parts) == 2 {
			if parts[0] == "" {
				if parts[1] == "" {
					lval.val = NewExpression([]Ex{blankType})
				} else if delim == "_" && parts[1] == "." {
					lval.val = NewExpression([]Ex{&Symbol{"Optional"}, NewExpression([]Ex{blankType})})
				} else {
					lval.val = NewExpression([]Ex{blankType, &Symbol{parts[1]}})
				}
				return PATTERN
			} else {
				if parts[1] == "" {
					lval.val = NewExpression([]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
				} else if delim == "_" && parts[1] == "." {
					lval.val = NewExpression([]Ex{&Symbol{"Optional"}, NewExpression([]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})})
				} else {
					lval.val = NewExpression([]Ex{&Symbol{"Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType, &Symbol{parts[1]}})})
				}
				return PATTERN
			}
		}
		lval.val = NewExpression([]Ex{&Symbol{"Error"}, &String{"Pattern parse error."}})
		return PATTERN
	}
yyrule53: // {contextedIdent}
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
