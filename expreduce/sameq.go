package expreduce

import (
	"math"

	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func IsSameQ(a expreduceapi.Ex, b expreduceapi.Ex, cl *logging.CASLogger) bool {
	aFlt, aIsFlt := a.(*Flt)
	bFlt, bIsFlt := b.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, bIsInteger := b.(*Integer)
	_, aIsString := a.(*String)
	_, bIsString := b.(*String)
	_, aIsSymbol := a.(*Symbol)
	_, bIsSymbol := b.(*Symbol)
	_, aIsRational := a.(*Rational)
	_, bIsRational := b.(*Rational)
	_, aIsComplex := a.(*Complex)
	_, bIsComplex := b.(*Complex)
	_, aIsExpression := a.(expreduceapi.ExpressionInterface)
	_, bIsExpression := b.(expreduceapi.ExpressionInterface)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) || (aIsRational && bIsRational) || (aIsComplex && bIsComplex) {
		// a and b are identical raw types
		if aIsFlt && bIsFlt {
			// This is important, without it e.g. NestWhileList[(# + 3/#)/2 &, 1.0, UnsameQ, 2] never converges
			// https://stackoverflow.com/questions/46136886/comparing-floats-by-ignoring-last-bit-in-golang
			aVal, _ := aFlt.Val.Float64()
			bVal, _ := bFlt.Val.Float64()

			if math.IsInf(aVal, 0) || math.IsInf(bVal, 0) {
				return a.IsEqual(b) == "EQUAL_TRUE"
			} else {
				return almostEqual(aVal, bVal)
			}
		} else {
			return a.IsEqual(b) == "EQUAL_TRUE"
		}
	} else if aIsExpression && bIsExpression {
		return a.Hash() == b.Hash()
	}

	// This should never happen
	return false
}

func almostEqual(a, b float64) bool {
	ai, bi := int64(math.Float64bits(a)), int64(math.Float64bits(b))
	return a == b || -1 <= ai-bi && ai-bi <= 1
}
