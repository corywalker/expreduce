// CAUTION: Generated file - DO NOT EDIT.

package expreduce

import __yyfmt__ "fmt"

import (
	"math/big"
	"strings"
	/*"fmt"*/)

type CalcSymType struct {
	yys    int
	val    Ex
	valSeq []Ex
}

type CalcXError struct {
	state, xsym int
}

const (
	CalcDefault     = 57398
	CalcEofCode     = 57344
	ALTSYM          = 57369
	ANDSYM          = 57373
	APPLYSYM        = 57391
	COLONSYM        = 57368
	COMMASYM        = 57351
	CONDITIONSYM    = 57367
	DIVSYM          = 57386
	DOTSYM          = 57387
	EQUALSYM        = 57381
	EXCLAMATIONSYM  = 57390
	EXPSYM          = 57388
	FLOAT           = 57346
	FUNCAPPSYM      = 57393
	FUNCTIONSYM     = 57359
	GETSYM          = 57395
	GREATEREQUALSYM = 57378
	GREATERSYM      = 57379
	INTEGER         = 57347
	LBRACKETSYM     = 57353
	LCURLYSYM       = 57355
	LESSEQUALSYM    = 57376
	LESSSYM         = 57377
	LPARSYM         = 57349
	MAPSYM          = 57392
	MESSAGENAMESYM  = 57397
	MINUSSYM        = 57384
	MULTSYM         = 57385
	NAME            = 57357
	ORSYM           = 57372
	PATTERN         = 57358
	PATTESTSYM      = 57394
	PLUSSYM         = 57383
	POSTFIXSYM      = 57362
	RBRACKETSYM     = 57354
	RCURLYSYM       = 57356
	REPEATEDNULLSYM = 57371
	REPEATEDSYM     = 57370
	REPLACEALLSYM   = 57364
	REPLACEREPSYM   = 57363
	RPARSYM         = 57350
	RULEDELAYEDSYM  = 57365
	RULESYM         = 57366
	SAMESYM         = 57375
	SEMISYM         = 57352
	SETDELAYEDSYM   = 57360
	SETSYM          = 57361
	SLOTSYM         = 57396
	SPANSYM         = 57382
	STRING          = 57348
	STRINGJOINSYM   = 57389
	UNEQUALSYM      = 57380
	UNSAMESYM       = 57374
	CalcErrCode     = 57345

	CalcMaxDepth = 200
	CalcTabOfs   = -65
)

var (
	CalcXLAT = map[int]int{
		57347: 0,  // INTEGER (106x)
		57357: 1,  // NAME (106x)
		57390: 2,  // EXCLAMATIONSYM (105x)
		57346: 3,  // FLOAT (105x)
		57395: 4,  // GETSYM (105x)
		57355: 5,  // LCURLYSYM (105x)
		57349: 6,  // LPARSYM (105x)
		57384: 7,  // MINUSSYM (105x)
		57358: 8,  // PATTERN (105x)
		57396: 9,  // SLOTSYM (105x)
		57348: 10, // STRING (105x)
		57399: 11, // expr (87x)
		57351: 12, // COMMASYM (66x)
		57354: 13, // RBRACKETSYM (65x)
		57353: 14, // LBRACKETSYM (62x)
		57356: 15, // RCURLYSYM (62x)
		57344: 16, // $end (61x)
		57369: 17, // ALTSYM (61x)
		57373: 18, // ANDSYM (61x)
		57391: 19, // APPLYSYM (61x)
		57367: 20, // CONDITIONSYM (61x)
		57386: 21, // DIVSYM (61x)
		57387: 22, // DOTSYM (61x)
		57381: 23, // EQUALSYM (61x)
		57345: 24, // error (61x)
		57388: 25, // EXPSYM (61x)
		57393: 26, // FUNCAPPSYM (61x)
		57359: 27, // FUNCTIONSYM (61x)
		57378: 28, // GREATEREQUALSYM (61x)
		57379: 29, // GREATERSYM (61x)
		57376: 30, // LESSEQUALSYM (61x)
		57377: 31, // LESSSYM (61x)
		57392: 32, // MAPSYM (61x)
		57397: 33, // MESSAGENAMESYM (61x)
		57385: 34, // MULTSYM (61x)
		57372: 35, // ORSYM (61x)
		57394: 36, // PATTESTSYM (61x)
		57383: 37, // PLUSSYM (61x)
		57362: 38, // POSTFIXSYM (61x)
		57371: 39, // REPEATEDNULLSYM (61x)
		57370: 40, // REPEATEDSYM (61x)
		57364: 41, // REPLACEALLSYM (61x)
		57363: 42, // REPLACEREPSYM (61x)
		57365: 43, // RULEDELAYEDSYM (61x)
		57366: 44, // RULESYM (61x)
		57375: 45, // SAMESYM (61x)
		57352: 46, // SEMISYM (61x)
		57360: 47, // SETDELAYEDSYM (61x)
		57361: 48, // SETSYM (61x)
		57382: 49, // SPANSYM (61x)
		57389: 50, // STRINGJOINSYM (61x)
		57380: 51, // UNEQUALSYM (61x)
		57374: 52, // UNSAMESYM (61x)
		57350: 53, // RPARSYM (58x)
		57400: 54, // exprseq (3x)
		57368: 55, // COLONSYM (2x)
		57401: 56, // list (1x)
		57398: 57, // $default (0x)
	}

	CalcSymNames = []string{
		"INTEGER",
		"NAME",
		"EXCLAMATIONSYM",
		"FLOAT",
		"GETSYM",
		"LCURLYSYM",
		"LPARSYM",
		"MINUSSYM",
		"PATTERN",
		"SLOTSYM",
		"STRING",
		"expr",
		"COMMASYM",
		"RBRACKETSYM",
		"LBRACKETSYM",
		"RCURLYSYM",
		"$end",
		"ALTSYM",
		"ANDSYM",
		"APPLYSYM",
		"CONDITIONSYM",
		"DIVSYM",
		"DOTSYM",
		"EQUALSYM",
		"error",
		"EXPSYM",
		"FUNCAPPSYM",
		"FUNCTIONSYM",
		"GREATEREQUALSYM",
		"GREATERSYM",
		"LESSEQUALSYM",
		"LESSSYM",
		"MAPSYM",
		"MESSAGENAMESYM",
		"MULTSYM",
		"ORSYM",
		"PATTESTSYM",
		"PLUSSYM",
		"POSTFIXSYM",
		"REPEATEDNULLSYM",
		"REPEATEDSYM",
		"REPLACEALLSYM",
		"REPLACEREPSYM",
		"RULEDELAYEDSYM",
		"RULESYM",
		"SAMESYM",
		"SEMISYM",
		"SETDELAYEDSYM",
		"SETSYM",
		"SPANSYM",
		"STRINGJOINSYM",
		"UNEQUALSYM",
		"UNSAMESYM",
		"RPARSYM",
		"exprseq",
		"COLONSYM",
		"list",
		"$default",
	}

	CalcTokenLiteralStrings = map[int]string{}

	CalcReductions = map[int]struct{ xsym, components int }{
		0:  {0, 1},
		1:  {56, 0},
		2:  {56, 2},
		3:  {56, 2},
		4:  {11, 3},
		5:  {11, 3},
		6:  {11, 2},
		7:  {11, 3},
		8:  {11, 2},
		9:  {11, 2},
		10: {11, 2},
		11: {11, 6},
		12: {11, 4},
		13: {11, 3},
		14: {11, 3},
		15: {11, 3},
		16: {11, 3},
		17: {11, 2},
		18: {11, 3},
		19: {11, 3},
		20: {11, 3},
		21: {11, 3},
		22: {11, 3},
		23: {11, 3},
		24: {11, 2},
		25: {11, 2},
		26: {11, 3},
		27: {11, 3},
		28: {11, 3},
		29: {11, 3},
		30: {11, 3},
		31: {11, 3},
		32: {11, 3},
		33: {11, 3},
		34: {11, 3},
		35: {11, 3},
		36: {11, 3},
		37: {11, 3},
		38: {11, 3},
		39: {11, 3},
		40: {11, 3},
		41: {11, 3},
		42: {11, 3},
		43: {11, 3},
		44: {11, 3},
		45: {11, 3},
		46: {11, 3},
		47: {11, 3},
		48: {11, 3},
		49: {11, 3},
		50: {11, 2},
		51: {11, 1},
		52: {11, 2},
		53: {11, 2},
		54: {11, 3},
		55: {11, 3},
		56: {11, 1},
		57: {11, 1},
		58: {11, 1},
		59: {11, 1},
		60: {11, 1},
		61: {54, 0},
		62: {54, 1},
		63: {54, 3},
		64: {54, 2},
	}

	CalcXErrors = map[CalcXError]string{}

	CalcParseTab = [110][]uint16{
		// 0
		{64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 16: 64, 24: 64, 56: 66},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 67, 16: 65, 24: 68},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 14: 85, 16: 63, 94, 116, 97, 103, 89, 115, 108, 63, 90, 92, 84, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 82, 105, 104, 114, 119, 109, 107},
		{62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 16: 62, 24: 62},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 173},
		// 5
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 172},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 152, 4, 15: 4, 54: 170},
		{9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 12: 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 55: 167},
		{8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 12: 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 55: 165},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 164},
		// 10
		{163, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 12: 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 80},
		{7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 12: 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7},
		{6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 12: 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6},
		{5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 12: 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5},
		// 15
		{79, 73, 12, 78, 12, 71, 69, 12, 72, 75, 77, 81, 12, 12, 85, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 118, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12},
		{79, 73, 83, 78, 76, 71, 69, 48, 72, 75, 77, 81, 48, 48, 85, 48, 48, 48, 48, 97, 48, 89, 115, 48, 48, 90, 92, 48, 48, 48, 48, 48, 98, 118, 48, 48, 93, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 119, 48, 48, 48},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 162, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59},
		{79, 73, 57, 78, 76, 71, 69, 57, 72, 75, 77, 161, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57},
		{55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 12: 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55},
		// 20
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 152, 4, 4, 153, 54: 154},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 151},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 150},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 149},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 148},
		// 25
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 147},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 146},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 145},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 144},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 143},
		// 30
		{41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 12: 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41},
		{40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 12: 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 142},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 141},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 140},
		// 35
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 139},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 138},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 137},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 136},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 135},
		// 40
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 134},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 133},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 132},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 131},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 130},
		// 45
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 129},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 128},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 127},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 126},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 125},
		// 50
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 124},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 123},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 122},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 121},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 120},
		// 55
		{79, 73, 83, 78, 76, 71, 69, 10, 72, 75, 77, 81, 10, 10, 85, 10, 10, 10, 10, 97, 10, 10, 10, 10, 10, 10, 92, 10, 10, 10, 10, 10, 98, 118, 10, 10, 93, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10},
		{79, 73, 11, 78, 11, 71, 69, 11, 11, 11, 77, 81, 11, 11, 85, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 16, 16, 85, 16, 16, 16, 116, 97, 16, 89, 115, 108, 16, 90, 92, 16, 113, 112, 111, 110, 98, 118, 88, 16, 93, 86, 16, 16, 16, 16, 16, 16, 16, 106, 16, 16, 16, 114, 119, 109, 107, 16},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 17, 17, 85, 17, 17, 17, 17, 97, 17, 89, 115, 108, 17, 90, 92, 17, 113, 112, 111, 110, 98, 118, 88, 17, 93, 86, 17, 17, 17, 17, 17, 17, 17, 106, 17, 17, 17, 114, 119, 109, 107, 17},
		{79, 73, 83, 78, 76, 71, 69, 18, 72, 75, 77, 81, 18, 18, 85, 18, 18, 18, 18, 97, 18, 18, 18, 18, 18, 90, 92, 18, 18, 18, 18, 18, 98, 118, 18, 18, 93, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 119, 18, 18, 18},
		// 60
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 19, 19, 85, 19, 19, 19, 19, 97, 19, 89, 115, 19, 19, 90, 92, 19, 19, 19, 19, 19, 98, 118, 88, 19, 93, 86, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 119, 19, 19, 19},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 20, 20, 85, 20, 20, 20, 20, 97, 20, 89, 115, 108, 20, 90, 92, 20, 20, 112, 20, 20, 98, 118, 88, 20, 93, 86, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 114, 119, 109, 20, 20},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 21, 21, 85, 21, 21, 21, 21, 97, 21, 89, 115, 108, 21, 90, 92, 21, 21, 21, 21, 21, 98, 118, 88, 21, 93, 86, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 114, 119, 109, 21, 21},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 22, 22, 85, 22, 22, 22, 22, 97, 22, 89, 115, 108, 22, 90, 92, 22, 113, 112, 22, 110, 98, 118, 88, 22, 93, 86, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 114, 119, 109, 22, 22},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 23, 23, 85, 23, 23, 23, 23, 97, 23, 89, 115, 108, 23, 90, 92, 23, 113, 112, 23, 23, 98, 118, 88, 23, 93, 86, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 114, 119, 109, 23, 23},
		// 65
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 24, 24, 85, 24, 24, 24, 24, 97, 24, 89, 115, 108, 24, 90, 92, 24, 24, 24, 24, 24, 98, 118, 88, 24, 93, 86, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 114, 119, 24, 24, 24},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 25, 25, 85, 25, 25, 25, 25, 97, 25, 89, 115, 25, 25, 90, 92, 25, 25, 25, 25, 25, 98, 118, 88, 25, 93, 86, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 114, 119, 25, 25, 25},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 26, 26, 85, 26, 26, 26, 26, 97, 26, 89, 115, 108, 26, 90, 92, 26, 113, 112, 111, 110, 98, 118, 88, 26, 93, 86, 26, 26, 26, 26, 26, 26, 26, 106, 26, 26, 26, 114, 119, 109, 26, 26},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 27, 27, 85, 27, 27, 27, 27, 97, 27, 89, 115, 108, 27, 90, 92, 27, 113, 112, 111, 110, 98, 118, 88, 27, 93, 86, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 114, 119, 109, 27, 27},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 28, 28, 85, 28, 28, 94, 116, 97, 103, 89, 115, 108, 28, 90, 92, 28, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 28, 105, 104, 114, 119, 109, 107, 28},
		// 70
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 29, 29, 85, 29, 29, 94, 116, 97, 103, 89, 115, 108, 29, 90, 92, 29, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 29, 29, 104, 114, 119, 109, 107, 29},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 33, 33, 85, 33, 33, 94, 116, 97, 33, 89, 115, 108, 33, 90, 92, 33, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 33, 96, 95, 33, 33, 33, 33, 106, 33, 33, 33, 114, 119, 109, 107, 33},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 34, 34, 85, 34, 34, 94, 116, 97, 103, 89, 115, 108, 34, 90, 92, 34, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 34, 96, 95, 34, 34, 100, 99, 106, 34, 34, 34, 114, 119, 109, 107, 34},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 35, 35, 85, 35, 35, 94, 116, 97, 103, 89, 115, 108, 35, 90, 92, 35, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 35, 96, 95, 102, 35, 100, 99, 106, 35, 35, 35, 114, 119, 109, 107, 35},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 36, 36, 85, 36, 36, 94, 116, 97, 103, 89, 115, 108, 36, 90, 92, 36, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 36, 96, 95, 36, 36, 100, 99, 106, 36, 36, 36, 114, 119, 109, 107, 36},
		// 75
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 37, 37, 85, 37, 37, 94, 116, 97, 103, 89, 115, 108, 37, 90, 92, 37, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 37, 96, 95, 37, 37, 37, 99, 106, 37, 37, 37, 114, 119, 109, 107, 37},
		{79, 73, 38, 78, 76, 71, 69, 38, 72, 75, 77, 81, 38, 38, 85, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 92, 38, 38, 38, 38, 38, 98, 118, 38, 38, 93, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38},
		{79, 73, 39, 78, 76, 71, 69, 39, 72, 75, 77, 81, 39, 39, 85, 39, 39, 39, 39, 97, 39, 39, 39, 39, 39, 39, 92, 39, 39, 39, 39, 39, 98, 118, 39, 39, 93, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 42, 42, 85, 42, 42, 42, 116, 97, 42, 89, 115, 108, 42, 90, 92, 42, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 42, 96, 95, 42, 42, 42, 42, 106, 42, 42, 42, 114, 119, 109, 107, 42},
		{79, 73, 43, 78, 76, 71, 69, 43, 72, 75, 77, 81, 43, 43, 85, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 118, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43},
		// 80
		{79, 73, 44, 78, 76, 71, 69, 44, 72, 75, 77, 81, 44, 44, 85, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 92, 44, 44, 44, 44, 44, 44, 118, 44, 44, 93, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 45, 45, 85, 45, 45, 94, 116, 97, 103, 89, 115, 108, 45, 90, 92, 45, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 45, 96, 95, 102, 101, 100, 99, 106, 45, 45, 45, 114, 119, 109, 107, 45},
		{79, 73, 83, 78, 76, 71, 69, 46, 72, 75, 77, 81, 46, 46, 85, 46, 46, 46, 46, 97, 46, 46, 46, 46, 46, 90, 92, 46, 46, 46, 46, 46, 98, 118, 46, 46, 93, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 119, 46, 46, 46},
		{79, 73, 83, 78, 76, 71, 69, 47, 72, 75, 77, 81, 47, 47, 85, 47, 47, 47, 47, 97, 47, 47, 115, 47, 47, 90, 92, 47, 47, 47, 47, 47, 98, 118, 47, 47, 93, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 119, 47, 47, 47},
		{79, 73, 83, 78, 76, 71, 69, 49, 72, 75, 77, 81, 49, 49, 85, 49, 49, 49, 49, 97, 49, 89, 115, 49, 49, 90, 92, 49, 49, 49, 49, 49, 98, 118, 49, 49, 93, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 119, 49, 49, 49},
		// 85
		{79, 73, 83, 78, 76, 71, 69, 50, 72, 75, 77, 81, 50, 50, 85, 50, 50, 50, 50, 97, 50, 89, 115, 50, 50, 90, 92, 50, 50, 50, 50, 50, 98, 118, 88, 50, 93, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 119, 50, 50, 50},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 51, 51, 85, 51, 51, 51, 51, 97, 51, 89, 115, 51, 51, 90, 92, 51, 51, 51, 51, 51, 98, 118, 88, 51, 93, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 119, 51, 51, 51},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 3, 3, 85, 3, 17: 94, 116, 97, 103, 89, 115, 108, 25: 90, 92, 84, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 82, 105, 104, 114, 119, 109, 107},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 152, 4, 4, 54: 158},
		{12: 156, 155},
		// 90
		{53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 12: 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53},
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 157, 1, 1, 15: 1},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 2, 2, 85, 2, 17: 94, 116, 97, 103, 89, 115, 108, 25: 90, 92, 84, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 82, 105, 104, 114, 119, 109, 107},
		{12: 156, 159},
		{13: 160},
		// 95
		{54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 12: 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54},
		{79, 73, 83, 78, 76, 71, 69, 58, 72, 75, 77, 81, 58, 58, 85, 58, 58, 58, 58, 97, 58, 89, 115, 58, 58, 90, 92, 58, 58, 58, 58, 58, 98, 118, 58, 58, 93, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 119, 58, 58, 58},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 60, 60, 85, 60, 60, 94, 116, 97, 103, 89, 115, 108, 60, 90, 92, 84, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 60, 105, 104, 114, 119, 109, 107, 60},
		{13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 12: 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13},
		{79, 73, 83, 78, 76, 71, 69, 15, 72, 75, 77, 81, 15, 15, 85, 15, 15, 15, 15, 97, 15, 89, 115, 15, 15, 90, 92, 15, 15, 15, 15, 15, 98, 118, 88, 15, 93, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 119, 15, 15, 15},
		// 100
		{79, 73, 70, 78, 76, 71, 69, 74, 72, 75, 77, 166},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 30, 30, 85, 30, 30, 94, 116, 97, 30, 89, 115, 108, 30, 90, 92, 30, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 30, 96, 95, 30, 30, 30, 30, 106, 30, 30, 30, 114, 119, 109, 107, 30},
		{168, 169},
		{32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 12: 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32},
		{31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 12: 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31},
		// 105
		{12: 156, 15: 171},
		{52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 12: 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 56, 56, 85, 56, 56, 56, 56, 97, 56, 89, 115, 108, 56, 90, 92, 56, 113, 112, 111, 110, 98, 118, 88, 56, 93, 86, 56, 56, 56, 56, 56, 56, 56, 106, 56, 56, 56, 114, 119, 109, 107, 56},
		{79, 73, 83, 78, 76, 71, 69, 87, 72, 75, 77, 81, 14: 85, 17: 94, 116, 97, 103, 89, 115, 108, 25: 90, 92, 84, 113, 112, 111, 110, 98, 118, 88, 117, 93, 86, 91, 96, 95, 102, 101, 100, 99, 106, 82, 105, 104, 114, 119, 109, 107, 174},
		{61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 12: 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61},
	}
)

var CalcDebug = 0

type CalcLexer interface {
	Lex(lval *CalcSymType) int
	Error(s string)
}

type CalcLexerEx interface {
	CalcLexer
	Reduced(rule, state int, lval *CalcSymType) bool
}

func CalcSymName(c int) (s string) {
	x, ok := CalcXLAT[c]
	if ok {
		return CalcSymNames[x]
	}

	if c < 0x7f {
		return __yyfmt__.Sprintf("'%c'", c)
	}

	return __yyfmt__.Sprintf("%d", c)
}

func Calclex1(yylex CalcLexer, lval *CalcSymType) (n int) {
	n = yylex.Lex(lval)
	if n <= 0 {
		n = CalcEofCode
	}
	if CalcDebug >= 3 {
		__yyfmt__.Printf("\nlex %s(%#x %d), lval: %+v\n", CalcSymName(n), n, n, lval)
	}
	return n
}

func CalcParse(yylex CalcLexer) int {
	const yyError = 24

	yyEx, _ := yylex.(CalcLexerEx)
	var yyn int
	var yylval CalcSymType
	var yyVAL CalcSymType
	yyS := make([]CalcSymType, 200)

	Nerrs := 0   /* number of errors */
	Errflag := 0 /* error recovery flag */
	yyerrok := func() {
		if CalcDebug >= 2 {
			__yyfmt__.Printf("yyerrok()\n")
		}
		Errflag = 0
	}
	_ = yyerrok
	yystate := 0
	yychar := -1
	var yyxchar int
	var yyshift int
	yyp := -1
	goto yystack

ret0:
	return 0

ret1:
	return 1

yystack:
	/* put a state and value onto the stack */
	yyp++
	if yyp >= len(yyS) {
		nyys := make([]CalcSymType, len(yyS)*2)
		copy(nyys, yyS)
		yyS = nyys
	}
	yyS[yyp] = yyVAL
	yyS[yyp].yys = yystate

yynewstate:
	if yychar < 0 {
		yychar = Calclex1(yylex, &yylval)
		var ok bool
		if yyxchar, ok = CalcXLAT[yychar]; !ok {
			yyxchar = len(CalcSymNames) // > tab width
		}
	}
	if CalcDebug >= 4 {
		var a []int
		for _, v := range yyS[:yyp+1] {
			a = append(a, v.yys)
		}
		__yyfmt__.Printf("state stack %v\n", a)
	}
	row := CalcParseTab[yystate]
	yyn = 0
	if yyxchar < len(row) {
		if yyn = int(row[yyxchar]); yyn != 0 {
			yyn += CalcTabOfs
		}
	}
	switch {
	case yyn > 0: // shift
		yychar = -1
		yyVAL = yylval
		yystate = yyn
		yyshift = yyn
		if CalcDebug >= 2 {
			__yyfmt__.Printf("shift, and goto state %d\n", yystate)
		}
		if Errflag > 0 {
			Errflag--
		}
		goto yystack
	case yyn < 0: // reduce
	case yystate == 1: // accept
		if CalcDebug >= 2 {
			__yyfmt__.Println("accept")
		}
		goto ret0
	}

	if yyn == 0 {
		/* error ... attempt to resume parsing */
		switch Errflag {
		case 0: /* brand new error */
			if CalcDebug >= 1 {
				__yyfmt__.Printf("no action for %s in state %d\n", CalcSymName(yychar), yystate)
			}
			msg, ok := CalcXErrors[CalcXError{yystate, yyxchar}]
			if !ok {
				msg, ok = CalcXErrors[CalcXError{yystate, -1}]
			}
			if !ok && yyshift != 0 {
				msg, ok = CalcXErrors[CalcXError{yyshift, yyxchar}]
			}
			if !ok {
				msg, ok = CalcXErrors[CalcXError{yyshift, -1}]
			}
			if yychar > 0 {
				ls := CalcTokenLiteralStrings[yychar]
				if ls == "" {
					ls = CalcSymName(yychar)
				}
				if ls != "" {
					switch {
					case msg == "":
						msg = __yyfmt__.Sprintf("unexpected %s", ls)
					default:
						msg = __yyfmt__.Sprintf("unexpected %s, %s", ls, msg)
					}
				}
			}
			if msg == "" {
				msg = "syntax error"
			}
			yylex.Error(msg)
			Nerrs++
			fallthrough

		case 1, 2: /* incompletely recovered error ... try again */
			Errflag = 3

			/* find a state where "error" is a legal shift action */
			for yyp >= 0 {
				row := CalcParseTab[yyS[yyp].yys]
				if yyError < len(row) {
					yyn = int(row[yyError]) + CalcTabOfs
					if yyn > 0 { // hit
						if CalcDebug >= 2 {
							__yyfmt__.Printf("error recovery found error shift in state %d\n", yyS[yyp].yys)
						}
						yystate = yyn /* simulate a shift of "error" */
						goto yystack
					}
				}

				/* the current p has no shift on "error", pop stack */
				if CalcDebug >= 2 {
					__yyfmt__.Printf("error recovery pops state %d\n", yyS[yyp].yys)
				}
				yyp--
			}
			/* there is no state on the stack with an error shift ... abort */
			if CalcDebug >= 2 {
				__yyfmt__.Printf("error recovery failed\n")
			}
			goto ret1

		case 3: /* no shift yet; clobber input char */
			if CalcDebug >= 2 {
				__yyfmt__.Printf("error recovery discards %s\n", CalcSymName(yychar))
			}
			if yychar == CalcEofCode {
				goto ret1
			}

			yychar = -1
			goto yynewstate /* try again in the same state */
		}
	}

	r := -yyn
	x0 := CalcReductions[r]
	x, n := x0.xsym, x0.components
	yypt := yyp
	_ = yypt // guard against "declared and not used"

	yyp -= n
	if yyp+1 >= len(yyS) {
		nyys := make([]CalcSymType, len(yyS)*2)
		copy(nyys, yyS)
		yyS = nyys
	}
	yyVAL = yyS[yyp+1]

	/* consult goto table to find next state */
	exState := yystate
	yystate = int(CalcParseTab[yyS[yyp].yys][x]) + CalcTabOfs
	/* reduction by production r */
	if CalcDebug >= 2 {
		__yyfmt__.Printf("reduce using rule %v (%s), and goto state %d\n", r, CalcSymNames[x], yystate)
	}

	switch r {
	case 2:
		{
			yylex.(*Calclexer).expr = yyS[yypt-0].val
		}
	case 3:
		{
			yylex.(*Calclexer).expr = &Symbol{"System`Null"}
		}
	case 4:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"Internal`Parens"}, yyS[yypt-1].val})
		}
	case 5:
		{
			yyVAL.val = fullyAssoc("System`CompoundExpression", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 6:
		{
			yyVAL.val = fullyAssoc("System`CompoundExpression", yyS[yypt-1].val, &Symbol{"System`Null"})
		}
	case 7:
		{
			yyVAL.val = NewExpression([]Ex{
				&Symbol{"System`Times"},
				NewExpression([]Ex{
					&Symbol{"System`Factorial"},
					yyS[yypt-2].val,
				}),
				yyS[yypt-0].val,
			})
		}
	case 8:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Factorial"}, yyS[yypt-1].val})
		}
	case 9:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Not"}, yyS[yypt-0].val})
		}
	case 10:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Function"}, yyS[yypt-1].val})
		}
	case 11:
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{&Symbol{"System`Part"}, yyS[yypt-5].val}, yyS[yypt-2].valSeq...)
			yyVAL.val = ex
		}
	case 12:
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{yyS[yypt-3].val}, yyS[yypt-1].valSeq...)
			yyVAL.val = ex
		}
	case 13:
		{
			ex := NewEmptyExpression()
			ex.Parts = []Ex{&Symbol{"System`List"}}
			ex.Parts = append(ex.Parts, yyS[yypt-1].valSeq...)
			yyVAL.val = ex
		}
	case 14:
		{
			yyVAL.val = fullyAssoc("System`Plus", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 15:
		{
			yyVAL.val = fullyAssoc("System`Plus", yyS[yypt-2].val, NewExpression([]Ex{&Symbol{"System`Times"}, yyS[yypt-0].val, &Integer{big.NewInt(-1)}}))
		}
	case 16:
		{
			yyVAL.val = fullyAssoc("System`Times", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 17:
		{
			yyVAL.val = rightFullyAssoc("System`Times", yyS[yypt-1].val, yyS[yypt-0].val)
		}
	case 18:
		{
			yyVAL.val = NewExpression([]Ex{
				&Symbol{"System`Times"},
				yyS[yypt-2].val,
				NewExpression([]Ex{
					&Symbol{"System`Power"},
					yyS[yypt-0].val,
					&Integer{big.NewInt(-1)},
				}),
			})
		}
	case 19:
		{
			yyVAL.val = NewExpression([]Ex{
				&Symbol{"System`Power"},
				yyS[yypt-2].val,
				yyS[yypt-0].val,
			})
		}
	case 20:
		{
			yyVAL.val = NewExpression([]Ex{yyS[yypt-0].val, yyS[yypt-2].val})
		}
	case 21:
		{
			yyVAL.val = NewExpression([]Ex{yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 22:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`PatternTest"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 23:
		{
			yyVAL.val = fullyAssoc("System`Alternatives", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 24:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Repeated"}, yyS[yypt-1].val})
		}
	case 25:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`RepeatedNull"}, yyS[yypt-1].val})
		}
	case 26:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Apply"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 27:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Map"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 28:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Rule"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 29:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`RuleDelayed"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 30:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`ReplaceRepeated"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 31:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`ReplaceAll"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 32:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Condition"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 33:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Optional"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 34:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Optional"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 35:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Pattern"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 36:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Set"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 37:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`SetDelayed"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 38:
		{
			yyVAL.val = fullyAssoc("System`SameQ", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 39:
		{
			yyVAL.val = fullyAssoc("System`UnsameQ", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 40:
		{
			yyVAL.val = fullyAssoc("System`Equal", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 41:
		{
			yyVAL.val = fullyAssoc("System`Unequal", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 42:
		{
			yyVAL.val = fullyAssoc("System`Less", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 43:
		{
			yyVAL.val = fullyAssoc("System`LessEqual", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 44:
		{
			yyVAL.val = fullyAssoc("System`Greater", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 45:
		{
			yyVAL.val = fullyAssoc("System`GreaterEqual", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 46:
		{
			yyVAL.val = fullyAssoc("System`Span", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 47:
		{
			yyVAL.val = fullyAssoc("System`Dot", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 48:
		{
			yyVAL.val = fullyAssoc("System`And", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 49:
		{
			yyVAL.val = fullyAssoc("System`Or", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 50:
		{
			if integer, isInteger := yyS[yypt-0].val.(*Integer); isInteger {
				yyVAL.val = &Integer{integer.Val.Neg(integer.Val)}
			} else if flt, isFlt := yyS[yypt-0].val.(*Flt); isFlt {
				yyVAL.val = &Flt{flt.Val.Neg(flt.Val)}
			} else {
				yyVAL.val = NewExpression([]Ex{&Symbol{"System`Times"}, yyS[yypt-0].val, &Integer{big.NewInt(-1)}})
			}
		}
	case 51:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Slot"}, &Integer{big.NewInt(1)}})
		}
	case 52:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Slot"}, yyS[yypt-0].val})
		}
	case 53:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Get"}, yyS[yypt-0].val})
		}
	case 54:
		{
			if sym, isSym := yyS[yypt-0].val.(*Symbol); isSym {
				yyVAL.val = fullyAssoc("System`MessageName", yyS[yypt-2].val, &String{sym.Name})
			} else {
				yyVAL.val = fullyAssoc("System`MessageName", yyS[yypt-2].val, yyS[yypt-0].val)
			}
		}
	case 55:
		{
			yyVAL.val = fullyAssoc("System`StringJoin", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 56:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 57:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 58:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 59:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 60:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 61:
		{
			yyVAL.valSeq = []Ex{}
		}
	case 62:
		{
			yyVAL.valSeq = append(yyVAL.valSeq, yyS[yypt-0].val)
		}
	case 63:
		{
			yyVAL.valSeq = append(yyVAL.valSeq, yyS[yypt-0].val)
		}
	case 64:
		{
			yyVAL.valSeq = append(yyVAL.valSeq, &Symbol{"System`Null"})
		}

	}

	if yyEx != nil && yyEx.Reduced(r, exState, &yyVAL) {
		return -1
	}
	goto yystack /* stack new state and value */
}

/*  start  of  programs  */

func fullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(lhs, op)
	if isOp {
		opExpr.Parts = append(opExpr.Parts, rhs)
		return opExpr
	}
	return NewExpression([]Ex{&Symbol{op}, lhs, rhs})
}

func rightFullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(rhs, op)
	if isOp {
		opExpr.Parts = append([]Ex{opExpr.Parts[0], lhs}, opExpr.Parts[1:]...)
		return opExpr
	}
	return NewExpression([]Ex{&Symbol{op}, lhs, rhs})
}

func removeParens(ex Ex) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		for i := range expr.Parts {
			parens, isParens := NewEmptyExpression(), true
			for isParens {
				parens, isParens = HeadAssertion(expr.Parts[i], "Internal`Parens")
				if isParens {
					expr.Parts[i] = parens.Parts[1]
				}
			}
			removeParens(expr.Parts[i])
		}
	}
	return
}

func addContextAndDefine(e Ex, context string, contextPath []string, es *EvalState) {
	if sym, isSym := e.(*Symbol); isSym {
		if !strings.Contains(sym.Name, "`") {
			for _, toTry := range contextPath {
				if es.IsDef(toTry + sym.Name) {
					sym.Name = toTry + sym.Name
					return
				}
			}
			sym.Name = context + sym.Name
		}
		es.MarkSeen(sym.Name)
	}
	expr, isExpr := e.(*Expression)
	if isExpr {
		for _, part := range expr.Parts {
			addContextAndDefine(part, context, contextPath, es)
		}
	}
}

func Interp(line string, es *EvalState) Ex {
	// If we want the ability to parse multiple statements without the need
	// for them to be separated by newlines, perhaps we should start with the
	// first line and evaluate it. If it produces an error, then we should
	// evaluate the first and second lines together, and so on. Once the
	// lines finally produce a valid expression, we can add that parsed
	// expression to the list of statements. Actually, we should read until the
	// lines no longer produce a valid expression or until we reach EOF.
	lex := newLexer(line + "\n")
	CalcParse(lex)

	parsed := lex.expr
	/*fmt.Printf("%v\n", parsed)*/
	// This can happen when we only enter a comment.
	if parsed == nil {
		return &Symbol{"System`Null"}
	}
	// Remove outer parens
	parens, isParens := NewEmptyExpression(), true
	for isParens {
		parens, isParens = HeadAssertion(parsed, "Internal`Parens")
		if isParens {
			parsed = parens.Parts[1]
		}
	}
	removeParens(parsed)
	context := es.GetStringDef("System`$Context", "")
	contextPathEx := es.GetListDef("System`$ContextPath")
	contextPath := []string{}
	for _, pathPart := range contextPathEx.Parts[1:] {
		contextPath = append(contextPath, pathPart.(*String).Val)
	}
	addContextAndDefine(parsed, context, contextPath, es)
	return parsed
}

func EvalInterp(line string, es *EvalState) Ex {
	return Interp(line, es).Eval(es)
}

func EvalInterpMany(doc string, es *EvalState) Ex {
	var last Ex
	for _, expr := range strings.Split(doc, "\n\n\n") {
		if len(strings.TrimSpace(expr)) == 0 {
			continue
		}
		last = EvalInterp(expr, es)
	}
	return last
}

func EasyRun(line string, es *EvalState) string {
	context, contextPath := ActualStringFormArgs(es)
	return EvalInterp(line, es).StringForm("InputForm", context, contextPath)
}
