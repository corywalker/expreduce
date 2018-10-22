package parens

import "github.com/cznic/wl"

var headsToTokens = map[string]int{
	"System`Alternatives":       124,
	"System`And":                57347,
	"System`Apply":              57348,
	"System`CompoundExpression": 59,
	"System`Condition":          57359,
	"System`Dot":                46,
	"System`Equal":              57380,
	"System`Factorial":          33,
	"System`Function":           38,
	"System`Greater":            62,
	"System`GreaterEqual":       57388,
	"System`Less":               60,
	"System`LessEqual":          57399,
	"System`Map":                57401,
	"System`Not":                33,
	"System`Or":                 57412,
	"System`PatternTest":        63,
	"System`Plus":               43,
	"System`Power":              94,
	"System`ReplaceAll":         57428,
	"System`ReplaceRepeated":    57429,
	"System`Rule":               57433,
	"System`RuleDelayed":        57434,
	"System`SameQ":              57435,
	"System`Set":                61,
	"System`SetDelayed":         57436,
	"System`Span":               57439,
	"System`StringJoin":         57445,
	"System`Times":              42,
	"System`Unequal":            57462,
	"System`UnsameQ":            57464,
}

func NeedsParens(thisHead string, PreviousHead string) bool {
	if PreviousHead == "<TOPLEVEL>" {
		return false
	}
	prevToken, prevTokenOk := headsToTokens[PreviousHead]
	thisToken, thisTokenOk := headsToTokens[thisHead]
	if prevTokenOk && thisTokenOk {
		prevPrec, prevPrecOk := wl.Precedence[prevToken]
		thisPrec, thisPrecOk := wl.Precedence[thisToken]
		if prevPrecOk && thisPrecOk {
			if prevPrec < thisPrec {
				return false
			}
		}
	}
	return true
}
