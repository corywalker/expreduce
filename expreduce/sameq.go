package expreduce

func IsSameQ(a Ex, b Ex, cl *CASLogger) bool {
	_, aIsFlt := a.(*Flt)
	_, bIsFlt := b.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, bIsInteger := b.(*Integer)
	_, aIsString := a.(*String)
	_, bIsString := b.(*String)
	_, aIsSymbol := a.(*Symbol)
	_, bIsSymbol := b.(*Symbol)
	_, aIsRational := a.(*Rational)
	_, bIsRational := b.(*Rational)
	aExpression, aIsExpression := a.(*Expression)
	bExpression, bIsExpression := b.(*Expression)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) || (aIsRational && bIsRational) {
		// a and b are identical raw types
		return a.IsEqual(b, cl) == "EQUAL_TRUE"
	} else if aIsExpression && bIsExpression {
		// a and b are both expressions
		return FunctionIsSameQ(aExpression.Parts, bExpression.Parts, cl)
	}

	// This should never happen
	return false
}

func FunctionIsSameQ(components []Ex, other_components []Ex, cl *CASLogger) bool {
	if len(components) != len(other_components) {
		return false
	}
	for i := range components {
		res := IsSameQ(components[i], other_components[i], cl)
		if !res {
			return false
		}
	}
	return true
}

