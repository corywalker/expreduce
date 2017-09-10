package expreduce

import "math"

func IsSameQ(a Ex, b Ex, cl *CASLogger) bool {
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
	_, aIsExpression := a.(*Expression)
	_, bIsExpression := b.(*Expression)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) || (aIsRational && bIsRational) {
		// a and b are identical raw types
		if aIsFlt && bIsFlt {
			// This is important, without it e.g. NestWhileList[(# + 3/#)/2 &, 1.0, UnsameQ, 2] never converges
			// https://stackoverflow.com/questions/46136886/comparing-floats-by-ignoring-last-bit-in-golang
			aVal, _ := aFlt.Val.Float64()
			bVal, _ := bFlt.Val.Float64()
			return almostEqual(aVal, bVal)
		} else {
			return a.IsEqual(b, cl) == "EQUAL_TRUE"
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