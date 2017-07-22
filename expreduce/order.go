package expreduce

func compareStrings(a string, b string) int64 {
	minchars := Min(len(a), len(b))
	for i := 0; i < minchars; i++ {
		if a[i] > b[i] {
			return -1
		} else if a[i] < b[i] {
			return 1
		}
	}
	if len(a) > len(b) {
		return -1
	} else if len(a) < len(b) {
		return 1
	}
	return 0
}

func ExOrder(a Ex, b Ex) int64 {
	// Support Flt, Integer, Rational, Expression, Symbol

	aAsSymbol, aIsSymbol := a.(*Symbol)
	bAsSymbol, bIsSymbol := b.(*Symbol)
	aAsString, aIsString := a.(*String)
	bAsString, bIsString := b.(*String)
	aAsExp, aIsExp := a.(*Expression)
	bAsExp, bIsExp := b.(*Expression)

	aAsFlt, aIsFlt := a.(*Flt)
	bAsFlt, bIsFlt := b.(*Flt)
	aAsInteger, aIsInteger := a.(*Integer)
	bAsInteger, bIsInteger := b.(*Integer)
	aAsRational, aIsRational := a.(*Rational)
	bAsRational, bIsRational := b.(*Rational)

	// Handle number comparisons
	// Merge Integer and Rational into Flt
	// TODO: possible precision, round off issue here.
	if aIsInteger {
		aAsFlt, aIsFlt = IntegerToFlt(aAsInteger)
	}
	if bIsInteger {
		bAsFlt, bIsFlt = IntegerToFlt(bAsInteger)
	}
	if aIsRational {
		aAsFlt, aIsFlt = RationalToFlt(aAsRational)
	}
	if bIsRational {
		bAsFlt, bIsFlt = RationalToFlt(bAsRational)
	}

	if aIsFlt && bIsFlt {
		initCmp := int64(bAsFlt.Val.Cmp(aAsFlt.Val))
		if initCmp == 0 && (aIsInteger && !bIsInteger) {
			return 1
		}
		if initCmp == 0 && (!aIsInteger && bIsInteger) {
			return -1
		}
		return initCmp
	}

	// Handle expression comparisons
	if aIsExp && bIsExp {
		_, aIsPow := HeadAssertion(aAsExp, "System`Power")
		_, bIsPow := HeadAssertion(bAsExp, "System`Power")
		_, aIsTimes := HeadAssertion(aAsExp, "System`Times")
		_, bIsTimes := HeadAssertion(bAsExp, "System`Times")
		if aIsPow && bIsTimes {
			return ExOrder(NewExpression([]Ex{
				&Symbol{"System`Times"},
				NewInt(1),
				aAsExp,
			}), b)
		}
		if aIsPow && !bIsPow {
			return ExOrder(a, NewExpression([]Ex{
				&Symbol{"System`Power"},
				bAsExp,
				NewInt(1),
			}))
		}
		if bIsPow && aIsTimes {
			return ExOrder(aAsExp, NewExpression([]Ex{
				&Symbol{"System`Times"},
				NewInt(1),
				bAsExp,
			}))
		}
		if !aIsPow && bIsPow {
			return ExOrder(NewExpression([]Ex{
				&Symbol{"System`Power"},
				aAsExp,
				NewInt(1),
			}), b)
		}
		timesMode := aIsTimes && bIsTimes
		if !timesMode {
			for i := 0; i < Min(len(aAsExp.Parts), len(bAsExp.Parts)); i++ {
				aPart, bPart := aAsExp.Parts[i], bAsExp.Parts[i]
				o := ExOrder(aPart, bPart)
				if o != 0 {
					return o
				}
			}
		}
		if timesMode {
			ai := len(aAsExp.Parts)-1
			bi := len(bAsExp.Parts)-1
			for ai >= 0 && bi >= 0 {
				aPart, bPart := aAsExp.Parts[ai], bAsExp.Parts[bi]
				ai, bi = ai-1, bi-1
				if numberQ(aPart) && numberQ(bPart) {
					continue
				}
				o := ExOrder(aPart, bPart)
				if o != 0 {
					return o
				}
			}
			for i := 0; i < Min(len(aAsExp.Parts), len(bAsExp.Parts)); i++ {
				aPart, bPart := aAsExp.Parts[i], bAsExp.Parts[i]
				if numberQ(aPart) && numberQ(bPart) {
					o := ExOrder(aPart, bPart)
					if o != 0 {
						return o
					}
				}
			}
		}
		if len(aAsExp.Parts) < len(bAsExp.Parts) {
			return 1
		} else if len(aAsExp.Parts) > len(bAsExp.Parts) {
			return -1
		} else {
			return 0
		}
	}

	// Symbol and string comparisons work in a similar way:
	if aIsSymbol && bIsSymbol {
		return compareStrings(aAsSymbol.Name, bAsSymbol.Name)
	}
	if aIsString && bIsString {
		return compareStrings(aAsString.Val, bAsString.Val)
	}

	// The remaining type combinations simply return -1 or 1:
	// Precedence order: numbers (flt), strings, symbols, expressions
	if aIsFlt && bIsString {
		return 1
	}
	if aIsFlt && bIsSymbol {
		return 1
	}
	if aIsFlt && bIsExp {
		return 1
	}

	if aIsString && bIsFlt {
		return -1
	}
	if aIsString && bIsSymbol {
		return 1
	}
	if aIsString && bIsExp {
		return 1
	}

	if aIsSymbol && bIsFlt {
		return -1
	}
	if aIsSymbol && bIsString {
		return -1
	}
	if aIsSymbol && bIsExp {
		_, bIsPow := HeadAssertion(bAsExp, "System`Power")
		if bIsPow {
			return ExOrder(NewExpression([]Ex{
				&Symbol{"System`Power"},
				a,
				NewInt(1),
			}), b)
		}
		_, bIsTimes := HeadAssertion(bAsExp, "System`Times")
		if bIsTimes {
			return ExOrder(NewExpression([]Ex{
				&Symbol{"System`Times"},
				NewInt(1),
				a,
			}), b)
		}
		return 1
	}

	if aIsExp && bIsFlt {
		return -1
	}
	if aIsExp && bIsString {
		return -1
	}
	if aIsExp && bIsSymbol {
		_, aIsPow := HeadAssertion(aAsExp, "System`Power")
		if aIsPow {
			return ExOrder(a, NewExpression([]Ex{
				&Symbol{"System`Power"},
				b,
				NewInt(1),
			}))
		}
		_, aIsTimes := HeadAssertion(aAsExp, "System`Times")
		if aIsTimes {
			return ExOrder(a, NewExpression([]Ex{
				&Symbol{"System`Times"},
				NewInt(1),
				b,
			}))
		}
		return -1
	}

	return -2
}
