package atoms

import (
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func min(x, y int) int {
	if x < y {
		return x
	}
	return y
}

func compareStrings(a string, b string) int64 {
	minchars := min(len(a), len(b))
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

func exprToN(e expreduceapi.Ex) expreduceapi.Ex {
	asInt, isInt := e.(*Integer)
	if isInt {
		toReturn, _ := IntegerToFlt(asInt)
		return toReturn
	}
	asRat, isRat := e.(*Rational)
	if isRat {
		toReturn, _ := RationalToFlt(asRat)
		return toReturn
	}
	return e
}

func ExOrder(a expreduceapi.Ex, b expreduceapi.Ex) int64 {
	// Support Flt, Integer, Rational, Expression, Symbol

	aAsSymbol, aIsSymbol := a.(*Symbol)
	bAsSymbol, bIsSymbol := b.(*Symbol)
	aAsString, aIsString := a.(*String)
	bAsString, bIsString := b.(*String)
	aAsExp, aIsExp := a.(expreduceapi.ExpressionInterface)
	bAsExp, bIsExp := b.(expreduceapi.ExpressionInterface)

	aAsFlt, aIsFlt := a.(*Flt)
	bAsFlt, bIsFlt := b.(*Flt)
	aAsInteger, aIsInteger := a.(*Integer)
	bAsInteger, bIsInteger := b.(*Integer)
	aAsRational, aIsRational := a.(*Rational)
	bAsRational, bIsRational := b.(*Rational)
	aAsComplex, aIsComplex := a.(*Complex)
	bAsComplex, bIsComplex := b.(*Complex)

	// Handle number comparisons
	if aIsInteger && bIsInteger {
		return int64(bAsInteger.Val.Cmp(aAsInteger.Val))
	}
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
	if aIsComplex {
		aAsFlt, aIsFlt = exprToN(aAsComplex.Re).(*Flt)
	}
	if bIsComplex {
		bAsFlt, bIsFlt = exprToN(bAsComplex.Re).(*Flt)
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
		if !aIsTimes && bIsTimes {
			return ExOrder(NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Times"),
				NewInt(1),
				aAsExp,
			}), b)
		}
		if aIsPow && !bIsPow {
			return ExOrder(a, NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Power"),
				bAsExp,
				NewInt(1),
			}))
		}
		if !bIsTimes && aIsTimes {
			return ExOrder(aAsExp, NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Times"),
				NewInt(1),
				bAsExp,
			}))
		}
		if !aIsPow && bIsPow {
			return ExOrder(NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Power"),
				aAsExp,
				NewInt(1),
			}), b)
		}
		timesMode := aIsTimes && bIsTimes
		if !timesMode {
			if len(aAsExp.GetParts()) < len(bAsExp.GetParts()) {
				return 1
			} else if len(aAsExp.GetParts()) > len(bAsExp.GetParts()) {
				return -1
			}
			for i := 0; i < len(aAsExp.GetParts()); i++ {
				aPart, bPart := aAsExp.GetParts()[i], bAsExp.GetParts()[i]
				o := ExOrder(aPart, bPart)
				if o != 0 {
					return o
				}
			}
			return 0
		}
		ai := len(aAsExp.GetParts()) - 1
		bi := len(bAsExp.GetParts()) - 1
		for ai >= 0 && bi >= 0 {
			aPart, bPart := aAsExp.GetParts()[ai], bAsExp.GetParts()[bi]
			ai, bi = ai-1, bi-1
			if NumberQ(aPart) && NumberQ(bPart) {
				continue
			}
			o := ExOrder(aPart, bPart)
			if o != 0 {
				return o
			}
		}
		for i := 0; i < min(len(aAsExp.GetParts()), len(bAsExp.GetParts())); i++ {
			aPart, bPart := aAsExp.GetParts()[i], bAsExp.GetParts()[i]
			if NumberQ(aPart) && NumberQ(bPart) {
				o := ExOrder(aPart, bPart)
				if o != 0 {
					return o
				}
			}
		}
		if len(aAsExp.GetParts()) < len(bAsExp.GetParts()) {
			return 1
		} else if len(aAsExp.GetParts()) > len(bAsExp.GetParts()) {
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
			return ExOrder(NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Power"),
				a,
				NewInt(1),
			}), b)
		}
		_, bIsTimes := HeadAssertion(bAsExp, "System`Times")
		if bIsTimes {
			return ExOrder(NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Times"),
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
			return ExOrder(a, NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Power"),
				b,
				NewInt(1),
			}))
		}
		_, aIsTimes := HeadAssertion(aAsExp, "System`Times")
		if aIsTimes {
			return ExOrder(a, NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Times"),
				NewInt(1),
				b,
			}))
		}
		return -1
	}

	return -2
}
