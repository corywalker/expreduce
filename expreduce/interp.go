// CAUTION: Generated file - DO NOT EDIT.

package expreduce

import __yyfmt__ "fmt"

import (
	"math/big"
	"strings"
)

type CalcSymType struct {
	yys    int
	val    Ex
	valSeq []Ex
}

type CalcXError struct {
	state, xsym int
}

const (
	CalcDefault     = 57397
	CalcEofCode     = 57344
	ALTSYM          = 57371
	ANDSYM          = 57389
	APPLYSYM        = 57369
	COLONSYM        = 57390
	COMMASYM        = 57351
	CONDITIONSYM    = 57359
	DIVSYM          = 57363
	DOTSYM          = 57395
	EQUALSYM        = 57373
	EXPSYM          = 57364
	FLOAT           = 57346
	FUNCAPPSYM      = 57368
	FUNCTIONSYM     = 57382
	GETSYM          = 57391
	GREATEREQUALSYM = 57386
	GREATERSYM      = 57387
	INTEGER         = 57347
	LBRACKETSYM     = 57353
	LCURLYSYM       = 57355
	LESSEQUALSYM    = 57384
	LESSSYM         = 57385
	LPARSYM         = 57349
	MAPSYM          = 57370
	MAPSYN          = 57396
	MESSAGENAMESYM  = 57380
	MINUSSYM        = 57361
	MULTSYM         = 57362
	NAME            = 57378
	ORSYM           = 57388
	PATTERN         = 57379
	PLUSSYM         = 57360
	POSTFIXSYM      = 57367
	RBRACKETSYM     = 57354
	RCURLYSYM       = 57356
	REPEATEDNULLSYM = 57394
	REPEATEDSYM     = 57393
	REPLACEALLSYM   = 57358
	REPLACEREPSYM   = 57357
	RPARSYM         = 57350
	RULEDELAYEDSYM  = 57366
	RULESYM         = 57365
	SAMESYM         = 57372
	SEMISYM         = 57352
	SETDELAYEDSYM   = 57376
	SETSYM          = 57375
	SLOTSYM         = 57377
	SPANSYM         = 57383
	STRING          = 57348
	STRINGJOINSYM   = 57381
	UNEQUALSYM      = 57374
	UNSAMESYM       = 57392
	CalcErrCode     = 57345

	CalcMaxDepth = 200
	CalcTabOfs   = -61
)

var (
	CalcXLAT = map[int]int{
		57347: 0,  // INTEGER (100x)
		57378: 1,  // NAME (100x)
		57346: 2,  // FLOAT (99x)
		57391: 3,  // GETSYM (99x)
		57355: 4,  // LCURLYSYM (99x)
		57349: 5,  // LPARSYM (99x)
		57361: 6,  // MINUSSYM (99x)
		57379: 7,  // PATTERN (99x)
		57377: 8,  // SLOTSYM (99x)
		57348: 9,  // STRING (99x)
		57398: 10, // expr (81x)
		57351: 11, // COMMASYM (62x)
		57354: 12, // RBRACKETSYM (61x)
		57353: 13, // LBRACKETSYM (58x)
		57356: 14, // RCURLYSYM (58x)
		57344: 15, // $end (57x)
		57371: 16, // ALTSYM (57x)
		57389: 17, // ANDSYM (57x)
		57369: 18, // APPLYSYM (57x)
		57359: 19, // CONDITIONSYM (57x)
		57363: 20, // DIVSYM (57x)
		57395: 21, // DOTSYM (57x)
		57373: 22, // EQUALSYM (57x)
		57345: 23, // error (57x)
		57364: 24, // EXPSYM (57x)
		57368: 25, // FUNCAPPSYM (57x)
		57382: 26, // FUNCTIONSYM (57x)
		57386: 27, // GREATEREQUALSYM (57x)
		57387: 28, // GREATERSYM (57x)
		57384: 29, // LESSEQUALSYM (57x)
		57385: 30, // LESSSYM (57x)
		57370: 31, // MAPSYM (57x)
		57380: 32, // MESSAGENAMESYM (57x)
		57362: 33, // MULTSYM (57x)
		57388: 34, // ORSYM (57x)
		57360: 35, // PLUSSYM (57x)
		57367: 36, // POSTFIXSYM (57x)
		57394: 37, // REPEATEDNULLSYM (57x)
		57393: 38, // REPEATEDSYM (57x)
		57358: 39, // REPLACEALLSYM (57x)
		57357: 40, // REPLACEREPSYM (57x)
		57366: 41, // RULEDELAYEDSYM (57x)
		57365: 42, // RULESYM (57x)
		57372: 43, // SAMESYM (57x)
		57352: 44, // SEMISYM (57x)
		57376: 45, // SETDELAYEDSYM (57x)
		57375: 46, // SETSYM (57x)
		57383: 47, // SPANSYM (57x)
		57381: 48, // STRINGJOINSYM (57x)
		57374: 49, // UNEQUALSYM (57x)
		57392: 50, // UNSAMESYM (57x)
		57350: 51, // RPARSYM (54x)
		57399: 52, // exprseq (3x)
		57390: 53, // COLONSYM (2x)
		57400: 54, // list (1x)
		57397: 55, // $default (0x)
		57396: 56, // MAPSYN (0x)
	}

	CalcSymNames = []string{
		"INTEGER",
		"NAME",
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
		"MAPSYN",
	}

	CalcTokenLiteralStrings = map[int]string{}

	CalcReductions = map[int]struct{ xsym, components int }{
		0:  {0, 1},
		1:  {54, 0},
		2:  {54, 2},
		3:  {54, 2},
		4:  {10, 3},
		5:  {10, 3},
		6:  {10, 2},
		7:  {10, 2},
		8:  {10, 6},
		9:  {10, 4},
		10: {10, 3},
		11: {10, 3},
		12: {10, 3},
		13: {10, 3},
		14: {10, 2},
		15: {10, 3},
		16: {10, 3},
		17: {10, 3},
		18: {10, 3},
		19: {10, 3},
		20: {10, 2},
		21: {10, 2},
		22: {10, 3},
		23: {10, 3},
		24: {10, 3},
		25: {10, 3},
		26: {10, 3},
		27: {10, 3},
		28: {10, 3},
		29: {10, 3},
		30: {10, 3},
		31: {10, 3},
		32: {10, 3},
		33: {10, 3},
		34: {10, 3},
		35: {10, 3},
		36: {10, 3},
		37: {10, 3},
		38: {10, 3},
		39: {10, 3},
		40: {10, 3},
		41: {10, 3},
		42: {10, 3},
		43: {10, 3},
		44: {10, 3},
		45: {10, 3},
		46: {10, 2},
		47: {10, 1},
		48: {10, 2},
		49: {10, 2},
		50: {10, 3},
		51: {10, 3},
		52: {10, 1},
		53: {10, 1},
		54: {10, 1},
		55: {10, 1},
		56: {10, 1},
		57: {52, 0},
		58: {52, 1},
		59: {52, 3},
		60: {52, 2},
	}

	CalcXErrors = map[CalcXError]string{}

	CalcParseTab = [104][]uint16{
		// 0
		{60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 15: 60, 23: 60, 54: 62},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 63, 15: 61, 23: 64},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 13: 79, 15: 59, 87, 109, 90, 96, 83, 108, 101, 59, 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 77, 98, 97, 107, 112, 102, 100},
		{58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 15: 58, 23: 58},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 163},
		// 5
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 144, 4, 14: 4, 52: 161},
		{9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 11: 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 53: 158},
		{8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 11: 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 53: 156},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 155},
		{154, 14, 14, 14, 14, 14, 14, 14, 14, 14, 11: 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14},
		// 10
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 75},
		{7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 11: 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7},
		{6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 11: 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6},
		{5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11: 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5},
		{74, 68, 73, 12, 66, 65, 12, 67, 70, 72, 76, 12, 12, 79, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 91, 111, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12},
		// 15
		{74, 68, 73, 71, 66, 65, 47, 67, 70, 72, 76, 47, 47, 79, 47, 47, 47, 47, 90, 47, 83, 108, 47, 47, 84, 86, 47, 47, 47, 47, 47, 91, 111, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 112, 47, 47, 47},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 153, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55},
		{54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 11: 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 144, 4, 4, 145, 52: 146},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 143},
		// 20
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 142},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 141},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 140},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 139},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 138},
		// 25
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 137},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 136},
		{41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 11: 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41},
		{40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 11: 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 135},
		// 30
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 134},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 133},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 132},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 131},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 130},
		// 35
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 129},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 128},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 127},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 126},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 125},
		// 40
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 124},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 123},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 122},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 121},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 120},
		// 45
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 119},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 118},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 117},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 116},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 115},
		// 50
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 114},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 113},
		{74, 68, 73, 71, 66, 65, 10, 67, 70, 72, 76, 10, 10, 79, 10, 10, 10, 10, 90, 10, 10, 10, 10, 10, 10, 86, 10, 10, 10, 10, 10, 91, 111, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10},
		{74, 68, 73, 11, 66, 65, 11, 11, 11, 72, 76, 11, 11, 79, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 91, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 16, 16, 79, 16, 16, 16, 109, 90, 16, 83, 108, 101, 16, 84, 86, 16, 106, 105, 104, 103, 91, 111, 82, 16, 80, 16, 16, 16, 16, 16, 16, 16, 99, 16, 16, 16, 107, 112, 102, 100, 16},
		// 55
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 17, 17, 79, 17, 17, 17, 17, 90, 17, 83, 108, 101, 17, 84, 86, 17, 106, 105, 104, 103, 91, 111, 82, 17, 80, 17, 17, 17, 17, 17, 17, 17, 99, 17, 17, 17, 107, 112, 102, 100, 17},
		{74, 68, 73, 71, 66, 65, 18, 67, 70, 72, 76, 18, 18, 79, 18, 18, 18, 18, 90, 18, 18, 18, 18, 18, 84, 86, 18, 18, 18, 18, 18, 91, 111, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 112, 18, 18, 18},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 19, 19, 79, 19, 19, 19, 19, 90, 19, 83, 108, 19, 19, 84, 86, 19, 19, 19, 19, 19, 91, 111, 82, 19, 80, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 112, 19, 19, 19},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 20, 20, 79, 20, 20, 20, 20, 90, 20, 83, 108, 101, 20, 84, 86, 20, 20, 105, 20, 20, 91, 111, 82, 20, 80, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 107, 112, 102, 20, 20},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 21, 21, 79, 21, 21, 21, 21, 90, 21, 83, 108, 101, 21, 84, 86, 21, 21, 21, 21, 21, 91, 111, 82, 21, 80, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 107, 112, 102, 21, 21},
		// 60
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 22, 22, 79, 22, 22, 22, 22, 90, 22, 83, 108, 101, 22, 84, 86, 22, 106, 105, 22, 103, 91, 111, 82, 22, 80, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 107, 112, 102, 22, 22},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 23, 23, 79, 23, 23, 23, 23, 90, 23, 83, 108, 101, 23, 84, 86, 23, 106, 105, 23, 23, 91, 111, 82, 23, 80, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 107, 112, 102, 23, 23},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 24, 24, 79, 24, 24, 24, 24, 90, 24, 83, 108, 101, 24, 84, 86, 24, 24, 24, 24, 24, 91, 111, 82, 24, 80, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 107, 112, 24, 24, 24},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 25, 25, 79, 25, 25, 25, 25, 90, 25, 83, 108, 25, 25, 84, 86, 25, 25, 25, 25, 25, 91, 111, 82, 25, 80, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 107, 112, 25, 25, 25},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 26, 26, 79, 26, 26, 26, 26, 90, 26, 83, 108, 101, 26, 84, 86, 26, 106, 105, 104, 103, 91, 111, 82, 26, 80, 26, 26, 26, 26, 26, 26, 26, 99, 26, 26, 26, 107, 112, 102, 26, 26},
		// 65
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 27, 27, 79, 27, 27, 27, 27, 90, 27, 83, 108, 101, 27, 84, 86, 27, 106, 105, 104, 103, 91, 111, 82, 27, 80, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 107, 112, 102, 27, 27},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 28, 28, 79, 28, 28, 87, 109, 90, 96, 83, 108, 101, 28, 84, 86, 28, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 28, 98, 97, 107, 112, 102, 100, 28},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 29, 29, 79, 29, 29, 87, 109, 90, 96, 83, 108, 101, 29, 84, 86, 29, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 29, 29, 97, 107, 112, 102, 100, 29},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 33, 33, 79, 33, 33, 87, 109, 90, 33, 83, 108, 101, 33, 84, 86, 33, 106, 105, 104, 103, 91, 111, 82, 110, 80, 33, 89, 88, 33, 33, 33, 33, 99, 33, 33, 33, 107, 112, 102, 100, 33},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 34, 34, 79, 34, 34, 87, 109, 90, 96, 83, 108, 101, 34, 84, 86, 34, 106, 105, 104, 103, 91, 111, 82, 110, 80, 34, 89, 88, 34, 34, 93, 92, 99, 34, 34, 34, 107, 112, 102, 100, 34},
		// 70
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 35, 35, 79, 35, 35, 87, 109, 90, 96, 83, 108, 101, 35, 84, 86, 35, 106, 105, 104, 103, 91, 111, 82, 110, 80, 35, 89, 88, 95, 35, 93, 92, 99, 35, 35, 35, 107, 112, 102, 100, 35},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 36, 36, 79, 36, 36, 87, 109, 90, 96, 83, 108, 101, 36, 84, 86, 36, 106, 105, 104, 103, 91, 111, 82, 110, 80, 36, 89, 88, 36, 36, 93, 92, 99, 36, 36, 36, 107, 112, 102, 100, 36},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 37, 37, 79, 37, 37, 87, 109, 90, 96, 83, 108, 101, 37, 84, 86, 37, 106, 105, 104, 103, 91, 111, 82, 110, 80, 37, 89, 88, 37, 37, 37, 92, 99, 37, 37, 37, 107, 112, 102, 100, 37},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 38, 38, 79, 38, 38, 87, 109, 90, 96, 83, 108, 101, 38, 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 77, 98, 97, 107, 112, 102, 100, 38},
		{74, 68, 73, 71, 66, 65, 39, 67, 70, 72, 76, 39, 39, 79, 39, 39, 39, 39, 90, 39, 39, 39, 39, 39, 39, 86, 39, 39, 39, 39, 39, 91, 111, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39},
		// 75
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 42, 42, 79, 42, 42, 42, 109, 90, 42, 83, 108, 101, 42, 84, 86, 42, 106, 105, 104, 103, 91, 111, 82, 110, 80, 42, 89, 88, 42, 42, 42, 42, 99, 42, 42, 42, 107, 112, 102, 100, 42},
		{74, 68, 73, 71, 66, 65, 43, 67, 70, 72, 76, 43, 43, 79, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 86, 43, 43, 43, 43, 43, 91, 111, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 44, 44, 79, 44, 44, 87, 109, 90, 96, 83, 108, 101, 44, 84, 86, 44, 106, 105, 104, 103, 91, 111, 82, 110, 80, 44, 89, 88, 95, 94, 93, 92, 99, 44, 44, 44, 107, 112, 102, 100, 44},
		{74, 68, 73, 71, 66, 65, 45, 67, 70, 72, 76, 45, 45, 79, 45, 45, 45, 45, 90, 45, 45, 45, 45, 45, 84, 86, 45, 45, 45, 45, 45, 91, 111, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 112, 45, 45, 45},
		{74, 68, 73, 71, 66, 65, 46, 67, 70, 72, 76, 46, 46, 79, 46, 46, 46, 46, 90, 46, 46, 108, 46, 46, 84, 86, 46, 46, 46, 46, 46, 91, 111, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 112, 46, 46, 46},
		// 80
		{74, 68, 73, 71, 66, 65, 48, 67, 70, 72, 76, 48, 48, 79, 48, 48, 48, 48, 90, 48, 83, 108, 48, 48, 84, 86, 48, 48, 48, 48, 48, 91, 111, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 112, 48, 48, 48},
		{74, 68, 73, 71, 66, 65, 49, 67, 70, 72, 76, 49, 49, 79, 49, 49, 49, 49, 90, 49, 83, 108, 49, 49, 84, 86, 49, 49, 49, 49, 49, 91, 111, 82, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 112, 49, 49, 49},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 50, 50, 79, 50, 50, 50, 50, 90, 50, 83, 108, 50, 50, 84, 86, 50, 50, 50, 50, 50, 91, 111, 82, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 112, 50, 50, 50},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 3, 3, 79, 3, 16: 87, 109, 90, 96, 83, 108, 101, 24: 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 77, 98, 97, 107, 112, 102, 100},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 144, 4, 4, 52: 150},
		// 85
		{11: 148, 147},
		{52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 11: 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52},
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 149, 1, 1, 14: 1},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 2, 2, 79, 2, 16: 87, 109, 90, 96, 83, 108, 101, 24: 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 77, 98, 97, 107, 112, 102, 100},
		{11: 148, 151},
		// 90
		{12: 152},
		{53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 11: 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 56, 56, 79, 56, 56, 87, 109, 90, 96, 83, 108, 101, 56, 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 56, 98, 97, 107, 112, 102, 100, 56},
		{13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 11: 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13},
		{74, 68, 73, 71, 66, 65, 15, 67, 70, 72, 76, 15, 15, 79, 15, 15, 15, 15, 90, 15, 83, 108, 15, 15, 84, 86, 15, 15, 15, 15, 15, 91, 111, 82, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 112, 15, 15, 15},
		// 95
		{74, 68, 73, 71, 66, 65, 69, 67, 70, 72, 157},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 30, 30, 79, 30, 30, 87, 109, 90, 30, 83, 108, 101, 30, 84, 86, 30, 106, 105, 104, 103, 91, 111, 82, 110, 80, 30, 89, 88, 30, 30, 30, 30, 99, 30, 30, 30, 107, 112, 102, 100, 30},
		{159, 160},
		{32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 11: 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32},
		{31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 11: 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31},
		// 100
		{11: 148, 14: 162},
		{51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 11: 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51},
		{74, 68, 73, 71, 66, 65, 81, 67, 70, 72, 76, 13: 79, 16: 87, 109, 90, 96, 83, 108, 101, 24: 84, 86, 78, 106, 105, 104, 103, 91, 111, 82, 110, 80, 85, 89, 88, 95, 94, 93, 92, 99, 77, 98, 97, 107, 112, 102, 100, 164},
		{57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 11: 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57},
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
	const yyError = 23

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
			Calcrcvr.lval.val = yyS[yypt-0].val
		}
	case 3:
		{
			Calcrcvr.lval.val = &Symbol{"System`Null"}
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
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Function"}, yyS[yypt-1].val})
		}
	case 8:
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{&Symbol{"System`Part"}, yyS[yypt-5].val}, yyS[yypt-2].valSeq...)
			yyVAL.val = ex
		}
	case 9:
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{yyS[yypt-3].val}, yyS[yypt-1].valSeq...)
			yyVAL.val = ex
		}
	case 10:
		{
			ex := NewEmptyExpression()
			ex.Parts = []Ex{&Symbol{"System`List"}}
			ex.Parts = append(ex.Parts, yyS[yypt-1].valSeq...)
			yyVAL.val = ex
		}
	case 11:
		{
			yyVAL.val = fullyAssoc("System`Plus", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 12:
		{
			yyVAL.val = fullyAssoc("System`Plus", yyS[yypt-2].val, NewExpression([]Ex{&Symbol{"System`Times"}, yyS[yypt-0].val, &Integer{big.NewInt(-1)}}))
		}
	case 13:
		{
			yyVAL.val = fullyAssoc("System`Times", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 14:
		{
			yyVAL.val = rightFullyAssoc("System`Times", yyS[yypt-1].val, yyS[yypt-0].val)
		}
	case 15:
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
	case 16:
		{
			yyVAL.val = NewExpression([]Ex{
				&Symbol{"System`Power"},
				yyS[yypt-2].val,
				yyS[yypt-0].val,
			})
		}
	case 17:
		{
			yyVAL.val = NewExpression([]Ex{yyS[yypt-0].val, yyS[yypt-2].val})
		}
	case 18:
		{
			yyVAL.val = NewExpression([]Ex{yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 19:
		{
			yyVAL.val = fullyAssoc("System`Alternatives", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 20:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Repeated"}, yyS[yypt-1].val})
		}
	case 21:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`RepeatedNull"}, yyS[yypt-1].val})
		}
	case 22:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Apply"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 23:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Map"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 24:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Rule"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 25:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`RuleDelayed"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 26:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`ReplaceRepeated"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 27:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`ReplaceAll"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 28:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Condition"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 29:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Optional"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 30:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Optional"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 31:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Pattern"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 32:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Set"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 33:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`SetDelayed"}, yyS[yypt-2].val, yyS[yypt-0].val})
		}
	case 34:
		{
			yyVAL.val = fullyAssoc("System`SameQ", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 35:
		{
			yyVAL.val = fullyAssoc("System`UnsameQ", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 36:
		{
			yyVAL.val = fullyAssoc("System`Equal", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 37:
		{
			yyVAL.val = fullyAssoc("System`Unequal", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 38:
		{
			yyVAL.val = fullyAssoc("System`Less", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 39:
		{
			yyVAL.val = fullyAssoc("System`LessEqual", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 40:
		{
			yyVAL.val = fullyAssoc("System`Greater", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 41:
		{
			yyVAL.val = fullyAssoc("System`GreaterEqual", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 42:
		{
			yyVAL.val = fullyAssoc("System`Span", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 43:
		{
			yyVAL.val = fullyAssoc("System`Dot", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 44:
		{
			yyVAL.val = fullyAssoc("System`And", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 45:
		{
			yyVAL.val = fullyAssoc("System`Or", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 46:
		{
			if integer, isInteger := yyS[yypt-0].val.(*Integer); isInteger {
				yyVAL.val = &Integer{integer.Val.Neg(integer.Val)}
			} else if flt, isFlt := yyS[yypt-0].val.(*Flt); isFlt {
				yyVAL.val = &Flt{flt.Val.Neg(flt.Val)}
			} else {
				yyVAL.val = NewExpression([]Ex{&Symbol{"System`Times"}, yyS[yypt-0].val, &Integer{big.NewInt(-1)}})
			}
		}
	case 47:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Slot"}, &Integer{big.NewInt(1)}})
		}
	case 48:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Slot"}, yyS[yypt-0].val})
		}
	case 49:
		{
			yyVAL.val = NewExpression([]Ex{&Symbol{"System`Get"}, yyS[yypt-0].val})
		}
	case 50:
		{
			if sym, isSym := yyS[yypt-0].val.(*Symbol); isSym {
				yyVAL.val = fullyAssoc("System`MessageName", yyS[yypt-2].val, &String{sym.Name})
			} else {
				yyVAL.val = fullyAssoc("System`MessageName", yyS[yypt-2].val, yyS[yypt-0].val)
			}
		}
	case 51:
		{
			yyVAL.val = fullyAssoc("System`StringJoin", yyS[yypt-2].val, yyS[yypt-0].val)
		}
	case 52:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 53:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 54:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 55:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 56:
		{
			yyVAL.val = yyS[yypt-0].val
		}
	case 57:
		{
			yyVAL.valSeq = []Ex{}
		}
	case 58:
		{
			yyVAL.valSeq = append(yyVAL.valSeq, yyS[yypt-0].val)
		}
	case 59:
		{
			yyVAL.valSeq = append(yyVAL.valSeq, yyS[yypt-0].val)
		}
	case 60:
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
	var parser CalcParser = CalcNewParser()
	parser.Parse(lex)

	parsed := parser.(*CalcParserImpl).lval.val
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
