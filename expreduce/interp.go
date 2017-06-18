//line interp.y:2
package expreduce

import __yyfmt__ "fmt"

//line interp.y:3
import (
	"math/big"
)

//line interp.y:13
type CalcSymType struct {
	yys    int
	val    Ex
	valSeq []Ex
}

const FLOAT = 57346
const INTEGER = 57347
const STRING = 57348
const LPARSYM = 57349
const RPARSYM = 57350
const COMMASYM = 57351
const SEMISYM = 57352
const LBRACKETSYM = 57353
const RBRACKETSYM = 57354
const LCURLYSYM = 57355
const RCURLYSYM = 57356
const REPLACEREPSYM = 57357
const REPLACEALLSYM = 57358
const CONDITIONSYM = 57359
const PLUSSYM = 57360
const MINUSSYM = 57361
const MULTSYM = 57362
const DIVSYM = 57363
const EXPSYM = 57364
const RULESYM = 57365
const RULEDELAYEDSYM = 57366
const POSTFIXSYM = 57367
const FUNCAPPSYM = 57368
const APPLYSYM = 57369
const MAPSYM = 57370
const PATTESTSYM = 57371
const ALTSYM = 57372
const SAMESYM = 57373
const EQUALSYM = 57374
const UNEQUALSYM = 57375
const SETSYM = 57376
const SETDELAYEDSYM = 57377
const SLOTSYM = 57378
const NAME = 57379
const PATTERN = 57380
const MESSAGENAMESYM = 57381
const STRINGJOINSYM = 57382
const EXCLAMATIONSYM = 57383
const FUNCTIONSYM = 57384
const SPANSYM = 57385
const LESSEQUALSYM = 57386
const LESSSYM = 57387
const GREATEREQUALSYM = 57388
const GREATERSYM = 57389
const ORSYM = 57390
const ANDSYM = 57391
const COLONSYM = 57392
const DOTSYM = 57393
const MAPSYN = 57394

var CalcToknames = [...]string{
	"$end",
	"error",
	"$unk",
	"FLOAT",
	"INTEGER",
	"STRING",
	"LPARSYM",
	"RPARSYM",
	"COMMASYM",
	"SEMISYM",
	"LBRACKETSYM",
	"RBRACKETSYM",
	"LCURLYSYM",
	"RCURLYSYM",
	"REPLACEREPSYM",
	"REPLACEALLSYM",
	"CONDITIONSYM",
	"PLUSSYM",
	"MINUSSYM",
	"MULTSYM",
	"DIVSYM",
	"EXPSYM",
	"RULESYM",
	"RULEDELAYEDSYM",
	"POSTFIXSYM",
	"FUNCAPPSYM",
	"APPLYSYM",
	"MAPSYM",
	"PATTESTSYM",
	"ALTSYM",
	"SAMESYM",
	"EQUALSYM",
	"UNEQUALSYM",
	"SETSYM",
	"SETDELAYEDSYM",
	"SLOTSYM",
	"NAME",
	"PATTERN",
	"MESSAGENAMESYM",
	"STRINGJOINSYM",
	"EXCLAMATIONSYM",
	"FUNCTIONSYM",
	"SPANSYM",
	"LESSEQUALSYM",
	"LESSSYM",
	"GREATEREQUALSYM",
	"GREATERSYM",
	"ORSYM",
	"ANDSYM",
	"COLONSYM",
	"DOTSYM",
	"MAPSYN",
	"'\\n'",
}
var CalcStatenames = [...]string{}

const CalcEofCode = 1
const CalcErrCode = 2
const CalcInitialStackSize = 16

//line interp.y:265

/*  start  of  programs  */

func fullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(lhs, op)
	if isOp {
		opExpr.Parts = append(opExpr.Parts, rhs)
		return opExpr
	}
	return NewExpression([]Ex{&Symbol{op}, lhs, rhs})
}

func removeParens(ex Ex) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		for i := range expr.Parts {
			parens, isParens := HeadAssertion(expr.Parts[i], "Internal`Parens")
			if isParens {
				expr.Parts[i] = parens.Parts[1]
			}
			removeParens(expr.Parts[i])
		}
	}
	return
}

func Interp(line string) Ex {
	lex := newLexer(line + "\n")
	var parser CalcParser = CalcNewParser()
	parser.Parse(lex)

	parsed := parser.(*CalcParserImpl).lval.val
	// Remove outer parens
	parens, isParens := NewEmptyExpression(), true
	for isParens {
		parens, isParens = HeadAssertion(parsed, "Internal`Parens")
		if isParens {
			parsed = parens.Parts[1]
		}
	}
	removeParens(parsed)
	return parsed
}

func EvalInterp(line string, es *EvalState) Ex {
	return Interp(line).Eval(es)
}

func EasyRun(line string, es *EvalState) string {
	return EvalInterp(line, es).StringForm("InputForm")
}

//line yacctab:1
var CalcExca = [...]int{
	-1, 1,
	1, -1,
	-2, 0,
	-1, 19,
	41, 0,
	-2, 10,
	-1, 56,
	41, 0,
	-2, 11,
	-1, 62,
	41, 0,
	-2, 9,
	-1, 72,
	29, 0,
	-2, 24,
}

const CalcNprod = 61
const CalcPrivate = 57344

var CalcTokenNames []string
var CalcStates []string

const CalcLast = 1480

var CalcAct = [...]int{

	25, 17, 5, 16, 57, 104, 99, 55, 56, 58,
	59, 98, 99, 99, 60, 103, 101, 3, 1, 61,
	62, 0, 58, 65, 66, 67, 64, 68, 69, 70,
	71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
	81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
	91, 92, 93, 94, 95, 96, 14, 15, 13, 6,
	0, 0, 0, 21, 58, 8, 0, 0, 100, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	33, 0, 0, 0, 0, 0, 0, 0, 0, 12,
	14, 15, 13, 6, 97, 0, 18, 21, 0, 8,
	102, 36, 37, 38, 22, 23, 24, 26, 27, 34,
	35, 28, 29, 32, 33, 30, 31, 42, 43, 44,
	40, 41, 10, 12, 11, 53, 54, 19, 20, 49,
	46, 45, 48, 47, 52, 51, 39, 50, 14, 15,
	13, 6, 0, 0, 18, 21, 0, 8, 0, 36,
	37, 38, 22, 23, 24, 26, 27, 34, 35, 28,
	29, 32, 33, 30, 31, 42, 43, 44, 40, 41,
	10, 12, 11, 53, 54, 19, 20, 49, 46, 45,
	48, 47, 52, 51, 39, 50, 14, 15, 13, 6,
	0, 0, 0, 21, 0, 8, 0, 36, 37, 38,
	22, 23, 24, 26, 27, 34, 35, 28, 29, 32,
	33, 30, 31, 42, 43, 44, 40, 41, 10, 12,
	11, 53, 54, 19, 20, 49, 46, 45, 48, 47,
	52, 51, 39, 50, 14, 15, 13, 6, 0, 0,
	0, 21, 0, 8, 0, 36, 37, 38, 22, 23,
	24, 26, 27, 34, 35, 28, 29, 32, 33, 30,
	31, 42, 43, 44, 40, 41, 10, 12, 11, 53,
	54, 19, 0, 49, 46, 45, 48, 47, 52, 51,
	39, 50, 14, 15, 13, 6, 0, 0, 0, 21,
	0, 8, 0, 36, 37, 38, 22, 23, 24, 26,
	27, 34, 35, 28, 29, 32, 33, 30, 31, 42,
	43, 44, 40, 0, 10, 12, 11, 53, 54, 19,
	0, 49, 46, 45, 48, 47, 52, 51, 39, 50,
	14, 15, 13, 6, 0, 0, 0, 21, 0, 8,
	0, 36, 37, 38, 22, 23, 24, 26, 27, 34,
	35, 0, 29, 32, 33, 30, 31, 42, 43, 44,
	0, 0, 10, 12, 11, 53, 54, 19, 0, 49,
	46, 45, 48, 47, 52, 51, 39, 50, 14, 15,
	13, 6, 0, 0, 0, 21, 0, 8, 0, 0,
	37, 38, 22, 23, 24, 26, 27, 34, 35, 0,
	29, 32, 33, 30, 31, 42, 43, 44, 0, 0,
	10, 12, 11, 53, 54, 19, 0, 49, 46, 45,
	48, 47, 52, 51, 39, 50, 14, 15, 13, 6,
	0, 0, 0, 21, 0, 8, 0, 0, 0, 38,
	22, 23, 24, 26, 27, 34, 35, 0, 29, 32,
	33, 30, 31, 42, 43, 44, 0, 0, 10, 12,
	11, 53, 54, 19, 0, 49, 46, 45, 48, 47,
	52, 51, 39, 50, 14, 15, 13, 6, 0, 0,
	0, 21, 0, 8, 0, 0, 0, 38, 22, 23,
	24, 26, 27, 34, 0, 0, 29, 32, 33, 30,
	31, 42, 43, 44, 0, 0, 10, 12, 11, 53,
	54, 19, 0, 49, 46, 45, 48, 47, 52, 51,
	39, 50, 14, 15, 13, 6, 0, 0, 0, 21,
	0, 8, 0, 0, 0, 0, 22, 23, 24, 26,
	27, 0, 0, 0, 29, 32, 33, 30, 31, 42,
	43, 44, 0, 0, 10, 12, 11, 53, 54, 19,
	0, 49, 46, 45, 48, 47, 52, 51, 39, 50,
	14, 15, 13, 6, 0, 0, 0, 21, 0, 8,
	0, 0, 0, 0, 22, 23, 24, 26, 27, 0,
	0, 0, 29, 32, 33, 30, 31, 42, 43, 44,
	0, 0, 10, 12, 11, 53, 54, 19, 0, 49,
	46, 45, 48, 47, 52, 51, 0, 50, 14, 15,
	13, 6, 0, 0, 0, 21, 0, 8, 0, 0,
	0, 0, 22, 23, 24, 26, 27, 0, 0, 0,
	29, 32, 33, 30, 0, 42, 43, 44, 0, 0,
	10, 12, 11, 53, 54, 19, 0, 49, 46, 45,
	48, 47, 52, 51, 0, 50, 14, 15, 13, 6,
	0, 0, 0, 21, 0, 8, 0, 0, 0, 0,
	22, 23, 24, 26, 27, 0, 0, 0, 29, 32,
	33, 30, 0, 42, 43, 44, 0, 0, 10, 12,
	11, 53, 54, 19, 0, 49, 46, 45, 48, 47,
	0, 51, 0, 50, 14, 15, 13, 6, 0, 0,
	0, 21, 0, 8, 0, 0, 0, 0, 22, 23,
	24, 26, 27, 0, 0, 0, 29, 32, 33, 30,
	0, 42, 43, 44, 0, 0, 10, 12, 11, 53,
	54, 19, 0, 49, 46, 45, 48, 47, 0, 0,
	0, 50, 14, 15, 13, 6, 0, 0, 0, 21,
	0, 8, 0, 0, 0, 0, 22, 23, 24, 26,
	27, 0, 0, 0, 29, 32, 33, 30, 0, 0,
	43, 44, 0, 0, 10, 12, 11, 53, 54, 19,
	0, 49, 46, 45, 48, 47, 0, 0, 0, 50,
	14, 15, 13, 6, 0, 0, 0, 21, 0, 8,
	0, 0, 0, 0, 22, 23, 24, 26, 27, 0,
	0, 0, 29, 32, 33, 30, 0, 0, 43, 44,
	0, 0, 10, 12, 11, 53, 54, 19, 0, 49,
	0, 45, 48, 47, 0, 0, 0, 50, 14, 15,
	13, 6, 0, 0, 0, 21, 0, 8, 0, 0,
	0, 0, 22, 23, 24, 26, 27, 0, 0, 0,
	29, 32, 33, 30, 0, 0, 43, 44, 0, 0,
	10, 12, 11, 53, 54, 19, 0, 49, 0, 0,
	48, 47, 0, 0, 0, 50, 14, 15, 13, 6,
	0, 0, 0, 21, 0, 8, 0, 0, 0, 0,
	22, 23, 24, 26, 27, 0, 0, 0, 29, 32,
	33, 30, 0, 0, 43, 44, 0, 0, 10, 12,
	11, 53, 54, 19, 0, 49, 0, 0, 0, 47,
	0, 0, 0, 50, 14, 15, 13, 6, 0, 0,
	0, 21, 0, 8, 0, 0, 0, 0, 22, 23,
	24, 26, 27, 0, 0, 0, 29, 32, 33, 30,
	0, 0, 43, 44, 0, 0, 10, 12, 11, 53,
	54, 19, 0, 49, 0, 14, 15, 13, 6, 0,
	0, 50, 21, 0, 8, 0, 0, 0, 0, 22,
	23, 24, 26, 27, 0, 0, 0, 29, 32, 33,
	30, 0, 0, 43, 0, 0, 0, 10, 12, 11,
	53, 54, 19, 0, 49, 0, 14, 15, 13, 6,
	0, 0, 50, 21, 0, 8, 0, 0, 0, 0,
	22, 23, 24, 26, 27, 0, 0, 0, 29, 32,
	33, 30, 0, 0, 0, 0, 0, 0, 10, 12,
	11, 53, 54, 19, 0, 49, 0, 14, 15, 13,
	6, 0, 0, 50, 21, 0, 8, 0, 0, 0,
	0, 22, 23, 24, 26, 27, 0, 0, 0, 29,
	32, 33, 30, 0, 0, 0, 0, 0, 0, 10,
	12, 11, 53, 54, 19, 0, 14, 15, 13, 6,
	0, 0, 0, 21, 50, 8, 0, 14, 15, 13,
	6, 23, 24, 26, 27, 0, 8, 0, 29, 32,
	33, 30, 0, 0, 0, 0, 0, 0, 10, 12,
	11, 53, 54, 19, 0, 14, 15, 13, 6, 10,
	12, 11, 21, 50, 8, 0, 0, 0, 0, 0,
	0, 24, 26, 27, 0, 0, 0, 29, 32, 33,
	30, 0, 0, 0, 0, 0, 0, 10, 12, 11,
	53, 54, 19, 0, 14, 15, 13, 6, 0, 0,
	0, 21, 50, 8, 0, 0, 0, 0, 0, 0,
	0, 26, 27, 0, 0, 0, 29, 32, 33, 30,
	0, 0, 0, 0, 0, 0, 10, 12, 11, 53,
	54, 19, 0, 14, 15, 13, 6, 0, 0, 0,
	21, 50, 8, 4, 0, 14, 15, 13, 6, 0,
	0, 27, 0, 0, 8, 29, 32, 33, 30, 0,
	9, 0, 0, 0, 0, 10, 12, 11, 53, 54,
	19, 0, 0, 0, 0, 0, 0, 10, 12, 11,
	50, 0, 7, 14, 15, 13, 6, 0, 0, 0,
	21, 0, 8, 0, 2, 0, 0, 0, 0, 0,
	0, 27, 0, 0, 0, 29, 32, 33, 30, 0,
	0, 0, 0, 0, 0, 10, 12, 11, 53, 54,
	19, 14, 15, 13, 6, 0, 0, 0, 21, 0,
	8, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 29, 32, 33, 30, 0, 0, 0,
	0, 0, 0, 10, 12, 11, 53, 0, 19, 14,
	15, 13, 6, 0, 0, 0, 21, 0, 8, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 29, 32, 33, 30, 0, 0, 0, 0, 0,
	0, 10, 12, 11, 53, 14, 15, 13, 6, 0,
	0, 0, 21, 0, 8, 0, 14, 15, 13, 6,
	0, 0, 0, 63, 0, 8, 0, 29, 0, 33,
	30, 9, 14, 15, 13, 6, 0, 10, 12, 11,
	53, 8, 0, 0, 0, 0, 0, 9, 10, 12,
	11, 0, 0, 7, 14, 15, 13, 6, 0, 0,
	0, 21, 0, 8, 10, 12, 11, 0, 0, 7,
	0, 0, 0, 0, 0, 0, 0, 0, 33, 0,
	0, 0, 0, 0, 0, 0, 10, 12, 11, 53,
}
var CalcPact = [...]int{

	-1000, 1241, -1000, -50, -52, 134, 1418, 1418, 1418, 1418,
	9, -1000, -1000, -1000, -1000, -1000, -1000, -1000, 1418, 1123,
	-1000, 1402, 1418, 1418, 1418, 1190, 1418, 1418, 1418, 1418,
	1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418,
	1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418, 1418,
	1418, 1418, 1418, 1418, 1418, 86, 1355, -3, 134, 1151,
	-1000, 182, 1355, 1418, 4, 1112, 1151, 1190, 1229, 1279,
	326, 1391, 1440, 614, 1355, 134, 470, 422, 374, 422,
	518, 566, 278, 230, 758, 1032, 991, 854, 806, 950,
	902, 1073, 1279, 710, 662, 52, 1317, -1000, -1000, 1418,
	3, -1000, 134, -7, -1000,
}
var CalcPgo = [...]int{

	0, 0, 4, 18, 17,
}
var CalcR1 = [...]int{

	0, 3, 3, 3, 3, 4, 1, 1, 1, 1,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
	1, 1, 1, 1, 1, 1, 1, 2, 2, 2,
	2,
}
var CalcR2 = [...]int{

	0, 0, 2, 3, 3, 1, 3, 3, 2, 3,
	2, 2, 2, 6, 4, 3, 3, 3, 3, 2,
	3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
	3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
	3, 3, 3, 3, 3, 3, 3, 2, 1, 2,
	3, 3, 1, 1, 1, 1, 1, 0, 1, 3,
	2,
}
var CalcChk = [...]int{

	-1000, -3, 53, -4, 2, -1, 7, 41, 13, 19,
	36, 38, 37, 6, 4, 5, 53, 53, 10, 41,
	42, 11, 18, 19, 20, -1, 21, 22, 25, 26,
	29, 30, 27, 28, 23, 24, 15, 16, 17, 50,
	34, 35, 31, 32, 33, 45, 44, 47, 46, 43,
	51, 49, 48, 39, 40, -1, -1, -2, -1, -1,
	5, -1, -1, 11, -2, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, 8, 14, 9,
	-2, 12, -1, 12, 12,
}
var CalcDef = [...]int{

	1, -2, 2, 0, 0, 5, 0, 0, 57, 0,
	48, 52, 53, 54, 55, 56, 3, 4, 8, -2,
	12, 57, 0, 0, 0, 19, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, -2, 0, 58, 47,
	49, 7, -2, 57, 0, 16, 17, 18, 20, 21,
	22, 23, -2, 25, 26, 27, 28, 29, 30, 31,
	32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
	42, 43, 44, 45, 46, 50, 51, 6, 15, 60,
	0, 14, 59, 0, 13,
}
var CalcTok1 = [...]int{

	1, 3, 3, 3, 3, 3, 3, 3, 3, 3,
	53,
}
var CalcTok2 = [...]int{

	2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
	12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
	32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
	42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
	52,
}
var CalcTok3 = [...]int{
	0,
}

var CalcErrorMessages = [...]struct {
	state int
	token int
	msg   string
}{}

//line yaccpar:1

/*	parser for yacc output	*/

var (
	CalcDebug        = 0
	CalcErrorVerbose = false
)

type CalcLexer interface {
	Lex(lval *CalcSymType) int
	Error(s string)
}

type CalcParser interface {
	Parse(CalcLexer) int
	Lookahead() int
}

type CalcParserImpl struct {
	lval  CalcSymType
	stack [CalcInitialStackSize]CalcSymType
	char  int
}

func (p *CalcParserImpl) Lookahead() int {
	return p.char
}

func CalcNewParser() CalcParser {
	return &CalcParserImpl{}
}

const CalcFlag = -1000

func CalcTokname(c int) string {
	if c >= 1 && c-1 < len(CalcToknames) {
		if CalcToknames[c-1] != "" {
			return CalcToknames[c-1]
		}
	}
	return __yyfmt__.Sprintf("tok-%v", c)
}

func CalcStatname(s int) string {
	if s >= 0 && s < len(CalcStatenames) {
		if CalcStatenames[s] != "" {
			return CalcStatenames[s]
		}
	}
	return __yyfmt__.Sprintf("state-%v", s)
}

func CalcErrorMessage(state, lookAhead int) string {
	const TOKSTART = 4

	if !CalcErrorVerbose {
		return "syntax error"
	}

	for _, e := range CalcErrorMessages {
		if e.state == state && e.token == lookAhead {
			return "syntax error: " + e.msg
		}
	}

	res := "syntax error: unexpected " + CalcTokname(lookAhead)

	// To match Bison, suggest at most four expected tokens.
	expected := make([]int, 0, 4)

	// Look for shiftable tokens.
	base := CalcPact[state]
	for tok := TOKSTART; tok-1 < len(CalcToknames); tok++ {
		if n := base + tok; n >= 0 && n < CalcLast && CalcChk[CalcAct[n]] == tok {
			if len(expected) == cap(expected) {
				return res
			}
			expected = append(expected, tok)
		}
	}

	if CalcDef[state] == -2 {
		i := 0
		for CalcExca[i] != -1 || CalcExca[i+1] != state {
			i += 2
		}

		// Look for tokens that we accept or reduce.
		for i += 2; CalcExca[i] >= 0; i += 2 {
			tok := CalcExca[i]
			if tok < TOKSTART || CalcExca[i+1] == 0 {
				continue
			}
			if len(expected) == cap(expected) {
				return res
			}
			expected = append(expected, tok)
		}

		// If the default action is to accept or reduce, give up.
		if CalcExca[i+1] != 0 {
			return res
		}
	}

	for i, tok := range expected {
		if i == 0 {
			res += ", expecting "
		} else {
			res += " or "
		}
		res += CalcTokname(tok)
	}
	return res
}

func Calclex1(lex CalcLexer, lval *CalcSymType) (char, token int) {
	token = 0
	char = lex.Lex(lval)
	if char <= 0 {
		token = CalcTok1[0]
		goto out
	}
	if char < len(CalcTok1) {
		token = CalcTok1[char]
		goto out
	}
	if char >= CalcPrivate {
		if char < CalcPrivate+len(CalcTok2) {
			token = CalcTok2[char-CalcPrivate]
			goto out
		}
	}
	for i := 0; i < len(CalcTok3); i += 2 {
		token = CalcTok3[i+0]
		if token == char {
			token = CalcTok3[i+1]
			goto out
		}
	}

out:
	if token == 0 {
		token = CalcTok2[1] /* unknown char */
	}
	if CalcDebug >= 3 {
		__yyfmt__.Printf("lex %s(%d)\n", CalcTokname(token), uint(char))
	}
	return char, token
}

func CalcParse(Calclex CalcLexer) int {
	return CalcNewParser().Parse(Calclex)
}

func (Calcrcvr *CalcParserImpl) Parse(Calclex CalcLexer) int {
	var Calcn int
	var CalcVAL CalcSymType
	var CalcDollar []CalcSymType
	_ = CalcDollar // silence set and not used
	CalcS := Calcrcvr.stack[:]

	Nerrs := 0   /* number of errors */
	Errflag := 0 /* error recovery flag */
	Calcstate := 0
	Calcrcvr.char = -1
	Calctoken := -1 // Calcrcvr.char translated into internal numbering
	defer func() {
		// Make sure we report no lookahead when not parsing.
		Calcstate = -1
		Calcrcvr.char = -1
		Calctoken = -1
	}()
	Calcp := -1
	goto Calcstack

ret0:
	return 0

ret1:
	return 1

Calcstack:
	/* put a state and value onto the stack */
	if CalcDebug >= 4 {
		__yyfmt__.Printf("char %v in %v\n", CalcTokname(Calctoken), CalcStatname(Calcstate))
	}

	Calcp++
	if Calcp >= len(CalcS) {
		nyys := make([]CalcSymType, len(CalcS)*2)
		copy(nyys, CalcS)
		CalcS = nyys
	}
	CalcS[Calcp] = CalcVAL
	CalcS[Calcp].yys = Calcstate

Calcnewstate:
	Calcn = CalcPact[Calcstate]
	if Calcn <= CalcFlag {
		goto Calcdefault /* simple state */
	}
	if Calcrcvr.char < 0 {
		Calcrcvr.char, Calctoken = Calclex1(Calclex, &Calcrcvr.lval)
	}
	Calcn += Calctoken
	if Calcn < 0 || Calcn >= CalcLast {
		goto Calcdefault
	}
	Calcn = CalcAct[Calcn]
	if CalcChk[Calcn] == Calctoken { /* valid shift */
		Calcrcvr.char = -1
		Calctoken = -1
		CalcVAL = Calcrcvr.lval
		Calcstate = Calcn
		if Errflag > 0 {
			Errflag--
		}
		goto Calcstack
	}

Calcdefault:
	/* default state action */
	Calcn = CalcDef[Calcstate]
	if Calcn == -2 {
		if Calcrcvr.char < 0 {
			Calcrcvr.char, Calctoken = Calclex1(Calclex, &Calcrcvr.lval)
		}

		/* look through exception table */
		xi := 0
		for {
			if CalcExca[xi+0] == -1 && CalcExca[xi+1] == Calcstate {
				break
			}
			xi += 2
		}
		for xi += 2; ; xi += 2 {
			Calcn = CalcExca[xi+0]
			if Calcn < 0 || Calcn == Calctoken {
				break
			}
		}
		Calcn = CalcExca[xi+1]
		if Calcn < 0 {
			goto ret0
		}
	}
	if Calcn == 0 {
		/* error ... attempt to resume parsing */
		switch Errflag {
		case 0: /* brand new error */
			Calclex.Error(CalcErrorMessage(Calcstate, Calctoken))
			Nerrs++
			if CalcDebug >= 1 {
				__yyfmt__.Printf("%s", CalcStatname(Calcstate))
				__yyfmt__.Printf(" saw %s\n", CalcTokname(Calctoken))
			}
			fallthrough

		case 1, 2: /* incompletely recovered error ... try again */
			Errflag = 3

			/* find a state where "error" is a legal shift action */
			for Calcp >= 0 {
				Calcn = CalcPact[CalcS[Calcp].yys] + CalcErrCode
				if Calcn >= 0 && Calcn < CalcLast {
					Calcstate = CalcAct[Calcn] /* simulate a shift of "error" */
					if CalcChk[Calcstate] == CalcErrCode {
						goto Calcstack
					}
				}

				/* the current p has no shift on "error", pop stack */
				if CalcDebug >= 2 {
					__yyfmt__.Printf("error recovery pops state %d\n", CalcS[Calcp].yys)
				}
				Calcp--
			}
			/* there is no state on the stack with an error shift ... abort */
			goto ret1

		case 3: /* no shift yet; clobber input char */
			if CalcDebug >= 2 {
				__yyfmt__.Printf("error recovery discards %s\n", CalcTokname(Calctoken))
			}
			if Calctoken == CalcEofCode {
				goto ret1
			}
			Calcrcvr.char = -1
			Calctoken = -1
			goto Calcnewstate /* try again in the same state */
		}
	}

	/* reduction by production Calcn */
	if CalcDebug >= 2 {
		__yyfmt__.Printf("reduce %v in:\n\t%v\n", Calcn, CalcStatname(Calcstate))
	}

	Calcnt := Calcn
	Calcpt := Calcp
	_ = Calcpt // guard against "declared and not used"

	Calcp -= CalcR2[Calcn]
	// Calcp is now the index of $0. Perform the default action. Iff the
	// reduced production is ε, $1 is possibly out of range.
	if Calcp+1 >= len(CalcS) {
		nyys := make([]CalcSymType, len(CalcS)*2)
		copy(nyys, CalcS)
		CalcS = nyys
	}
	CalcVAL = CalcS[Calcp+1]

	/* consult goto table to find next state */
	Calcn = CalcR1[Calcn]
	Calcg := CalcPgo[Calcn]
	Calcj := Calcg + CalcS[Calcp].yys + 1

	if Calcj >= CalcLast {
		Calcstate = CalcAct[Calcg]
	} else {
		Calcstate = CalcAct[Calcj]
		if CalcChk[Calcstate] != -Calcn {
			Calcstate = CalcAct[Calcg]
		}
	}
	// dummy call; replaced with literal code
	switch Calcnt {

	case 2:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:81
		{
			Calcrcvr.lval.val = &Symbol{"Null"}
		}
	case 4:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:83
		{
			Calcrcvr.lval.val = &Symbol{"Null"}
		}
	case 5:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:87
		{
			Calcrcvr.lval.val = CalcDollar[1].val
		}
	case 6:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:95
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Internal`Parens"}, CalcDollar[2].val})
		}
	case 7:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:99
		{
			CalcVAL.val = fullyAssoc("CompoundExpression", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 8:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:101
		{
			CalcVAL.val = fullyAssoc("CompoundExpression", CalcDollar[1].val, &Symbol{"Null"})
		}
	case 9:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:103
		{
			CalcVAL.val = NewExpression([]Ex{
				&Symbol{"Times"},
				NewExpression([]Ex{
					&Symbol{"Factorial"},
					CalcDollar[1].val,
				}),
				CalcDollar[3].val,
			})
		}
	case 10:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:113
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Factorial"}, CalcDollar[1].val})
		}
	case 11:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:115
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Not"}, CalcDollar[2].val})
		}
	case 12:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:117
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Function"}, CalcDollar[1].val})
		}
	case 13:
		CalcDollar = CalcS[Calcpt-6 : Calcpt+1]
		//line interp.y:119
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{&Symbol{"Part"}, CalcDollar[1].val}, CalcDollar[4].valSeq...)
			CalcVAL.val = ex
		}
	case 14:
		CalcDollar = CalcS[Calcpt-4 : Calcpt+1]
		//line interp.y:125
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{CalcDollar[1].val}, CalcDollar[3].valSeq...)
			CalcVAL.val = ex
		}
	case 15:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:131
		{
			ex := NewEmptyExpression()
			ex.Parts = []Ex{&Symbol{"List"}}
			ex.Parts = append(ex.Parts, CalcDollar[2].valSeq...)
			CalcVAL.val = ex
		}
	case 16:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:138
		{
			CalcVAL.val = fullyAssoc("Plus", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 17:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:140
		{
			CalcVAL.val = fullyAssoc("Plus", CalcDollar[1].val, NewExpression([]Ex{&Symbol{"Times"}, CalcDollar[3].val, &Integer{big.NewInt(-1)}}))
		}
	case 18:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:142
		{
			CalcVAL.val = fullyAssoc("Times", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 19:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:144
		{
			CalcVAL.val = fullyAssoc("Times", CalcDollar[1].val, CalcDollar[2].val)
		}
	case 20:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:146
		{
			CalcVAL.val = NewExpression([]Ex{
				&Symbol{"Times"},
				CalcDollar[1].val,
				NewExpression([]Ex{
					&Symbol{"Power"},
					CalcDollar[3].val,
					&Integer{big.NewInt(-1)},
				}),
			})
		}
	case 21:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:157
		{
			CalcVAL.val = NewExpression([]Ex{
				&Symbol{"Power"},
				CalcDollar[1].val,
				CalcDollar[3].val,
			})
		}
	case 22:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:164
		{
			CalcVAL.val = NewExpression([]Ex{CalcDollar[3].val, CalcDollar[1].val})
		}
	case 23:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:166
		{
			CalcVAL.val = NewExpression([]Ex{CalcDollar[1].val, CalcDollar[3].val})
		}
	case 24:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:168
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"PatternTest"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 25:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:170
		{
			CalcVAL.val = fullyAssoc("Alternatives", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 26:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:172
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Apply"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 27:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:174
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Map"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 28:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:176
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Rule"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 29:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:178
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"RuleDelayed"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 30:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:180
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"ReplaceRepeated"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 31:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:182
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"ReplaceAll"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 32:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:184
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Condition"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 33:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:186
		{
			if _, isPat := HeadAssertion(CalcDollar[1].val, "Pattern"); isPat {
				CalcVAL.val = NewExpression([]Ex{&Symbol{"Optional"}, CalcDollar[1].val, CalcDollar[3].val})
			} else {
				CalcVAL.val = NewExpression([]Ex{&Symbol{"Pattern"}, CalcDollar[1].val, CalcDollar[3].val})
			}
		}
	case 34:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:194
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Set"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 35:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:196
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"SetDelayed"}, CalcDollar[1].val, CalcDollar[3].val})
		}
	case 36:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:198
		{
			CalcVAL.val = fullyAssoc("SameQ", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 37:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:200
		{
			CalcVAL.val = fullyAssoc("Equal", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 38:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:202
		{
			CalcVAL.val = fullyAssoc("Unequal", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 39:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:204
		{
			CalcVAL.val = fullyAssoc("Less", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 40:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:206
		{
			CalcVAL.val = fullyAssoc("LessEqual", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 41:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:208
		{
			CalcVAL.val = fullyAssoc("Greater", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 42:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:210
		{
			CalcVAL.val = fullyAssoc("GreaterEqual", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 43:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:212
		{
			CalcVAL.val = fullyAssoc("Span", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 44:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:214
		{
			CalcVAL.val = fullyAssoc("Dot", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 45:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:216
		{
			CalcVAL.val = fullyAssoc("And", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 46:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:218
		{
			CalcVAL.val = fullyAssoc("Or", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 47:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:220
		{
			if integer, isInteger := CalcDollar[2].val.(*Integer); isInteger {
				CalcVAL.val = &Integer{integer.Val.Neg(integer.Val)}
			} else if flt, isFlt := CalcDollar[2].val.(*Flt); isFlt {
				CalcVAL.val = &Flt{flt.Val.Neg(flt.Val)}
			} else {
				CalcVAL.val = NewExpression([]Ex{&Symbol{"Times"}, CalcDollar[2].val, &Integer{big.NewInt(-1)}})
			}
		}
	case 48:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:230
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Slot"}, &Integer{big.NewInt(1)}})
		}
	case 49:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:232
		{
			CalcVAL.val = NewExpression([]Ex{&Symbol{"Slot"}, CalcDollar[2].val})
		}
	case 50:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:234
		{
			if sym, isSym := CalcDollar[3].val.(*Symbol); isSym {
				CalcVAL.val = fullyAssoc("MessageName", CalcDollar[1].val, &String{sym.Name})
			} else {
				CalcVAL.val = fullyAssoc("MessageName", CalcDollar[1].val, CalcDollar[3].val)
			}
		}
	case 51:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:242
		{
			CalcVAL.val = fullyAssoc("StringJoin", CalcDollar[1].val, CalcDollar[3].val)
		}
	case 52:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:244
		{
			CalcVAL.val = CalcDollar[1].val
		}
	case 53:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:246
		{
			CalcVAL.val = CalcDollar[1].val
		}
	case 54:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:248
		{
			CalcVAL.val = CalcDollar[1].val
		}
	case 55:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:250
		{
			CalcVAL.val = CalcDollar[1].val
		}
	case 56:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:252
		{
			CalcVAL.val = CalcDollar[1].val
		}
	case 57:
		CalcDollar = CalcS[Calcpt-0 : Calcpt+1]
		//line interp.y:256
		{
			CalcVAL.valSeq = []Ex{}
		}
	case 58:
		CalcDollar = CalcS[Calcpt-1 : Calcpt+1]
		//line interp.y:258
		{
			CalcVAL.valSeq = append(CalcVAL.valSeq, CalcDollar[1].val)
		}
	case 59:
		CalcDollar = CalcS[Calcpt-3 : Calcpt+1]
		//line interp.y:260
		{
			CalcVAL.valSeq = append(CalcVAL.valSeq, CalcDollar[3].val)
		}
	case 60:
		CalcDollar = CalcS[Calcpt-2 : Calcpt+1]
		//line interp.y:262
		{
			CalcVAL.valSeq = append(CalcVAL.valSeq, &Symbol{"Null"})
		}
	}
	goto Calcstack /* stack new state and value */
}
