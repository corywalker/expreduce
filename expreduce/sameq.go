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
	_, aIsExpression := a.(*Expression)
	_, bIsExpression := b.(*Expression)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) || (aIsRational && bIsRational) {
		// a and b are identical raw types
		return a.IsEqual(b, cl) == "EQUAL_TRUE"
	} else if aIsExpression && bIsExpression {
		return a.Hash() == b.Hash()
	}

	// This should never happen
	return false
}
