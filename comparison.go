package cas

import "bytes"

func (this *Expression) EvalEqual(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var isequal string = this.Parts[1].IsEqual(this.Parts[2], &es.CASLogger)
	if isequal == "EQUAL_UNK" {
		return this
	} else if isequal == "EQUAL_TRUE" {
		return &Symbol{"True"}
	} else if isequal == "EQUAL_FALSE" {
		return &Symbol{"False"}
	}

	return &Expression{[]Ex{&Symbol{"Error"}, &String{"Unexpected equality return value."}}}
}

func (this *Expression) ToStringEqual() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") == (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalSameQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var issame bool = IsSameQ(this.Parts[1], this.Parts[2], &es.CASLogger)
	if issame {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}

func (this *Expression) ToStringSameQ() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].String())
	buffer.WriteString(") === (")
	buffer.WriteString(this.Parts[2].String())
	buffer.WriteString(")")
	return buffer.String()
}

func IsMatchQRational(a *Rational, b *Expression, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	return IsMatchQ(
		&Expression{[]Ex{
			&Symbol{"Rational"},
			&Integer{a.Num},
			&Integer{a.Den},
		}},
		b, pm, cl)
}

func IsMatchQ(a Ex, b Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	// Special case for Except
	except, isExcept := HeadAssertion(b, "Except")
	if isExcept {
		if len(except.Parts) == 2 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), cl)
			return !matchq, pm
		} else if len(except.Parts) == 3 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), cl)
			if !matchq {
				matchqb, newPm := IsMatchQ(a, except.Parts[2], pm, cl)
				return matchqb, newPm
			}
			return false, pm
		}
	}
	// Special case for PatternTest
	patternTest, isPT := HeadAssertion(b, "PatternTest")
	if isPT {
		if len(patternTest.Parts) == 3 {
			matchq, newPD := IsMatchQ(a, patternTest.Parts[1], EmptyPD(), cl)
			if matchq {
				tmpEs := NewEvalStateNoLog()
				res := (&Expression{[]Ex{
					patternTest.Parts[2],
					a,
				}}).Eval(tmpEs)
				resSymbol, resIsSymbol := res.(*Symbol)
				if resIsSymbol {
					if resSymbol.Name == "True" {
						return true, newPD
					}
				}
			}
			return false, pm
		}
	}
	// Special case for Condition
	condition, isCond := HeadAssertion(b, "Condition")
	if isCond {
		if len(condition.Parts) == 3 {
			matchq, newPD := IsMatchQ(a, condition.Parts[1], EmptyPD(), cl)
			if matchq {
				tmpEs := NewEvalStateNoLog()
				res := condition.Parts[2].DeepCopy()
				res = ReplacePD(res, cl, newPD).Eval(tmpEs)
				resSymbol, resIsSymbol := res.(*Symbol)
				if resIsSymbol {
					if resSymbol.Name == "True" {
						return true, newPD
					}
				}
			}
		}
	}

	// Continue normally
	pm = CopyPD(pm)
	_, aIsFlt := a.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, aIsString := a.(*String)
	_, aIsSymbol := a.(*Symbol)
	aRational, aIsRational := a.(*Rational)
	bRational, bIsRational := b.(*Rational)
	aExpression, aIsExpression := a.(*Expression)
	bExpression, bIsExpression := b.(*Expression)

	// This initial value is just a randomly chosen placeholder
	// TODO, convert headStr to symbol type, have Ex implement getHead() Symbol
	headStr := "Unknown"
	if aIsFlt {
		headStr = "Real"
	} else if aIsInteger {
		headStr = "Integer"
	} else if aIsString {
		headStr = "String"
	} else if aIsExpression {
		headStr = aExpression.Parts[0].String()
	} else if aIsSymbol {
		headStr = "Symbol"
	} else if aIsRational {
		headStr = "Rational"
	}

	if IsBlankTypeOnly(b) {
		ibtc, ibtcNewPDs := IsBlankTypeCapturing(b, a, headStr, pm, cl)
		if ibtc {
			return true, ibtcNewPDs
		}
		return false, EmptyPD()
	}

	// Handle special case for matching Rational[a_Integer, b_Integer]
	if aIsRational && bIsExpression {
		return IsMatchQRational(aRational, bExpression, pm, cl)
	} else if aIsExpression && bIsRational {
		return IsMatchQRational(bRational, aExpression, pm, cl)
	}

	if aIsFlt || aIsInteger || aIsString || aIsSymbol || aIsRational {
		return IsSameQ(a, b, cl), EmptyPD()
	} else if !(aIsExpression && bIsExpression) {
		return false, EmptyPD()
	}

	aExpressionSym, aExpressionSymOk := aExpression.Parts[0].(*Symbol)
	bExpressionSym, bExpressionSymOk := bExpression.Parts[0].(*Symbol)
	if aExpressionSymOk && bExpressionSymOk {
		if aExpressionSym.Name == bExpressionSym.Name {
			if IsOrderless(aExpressionSym) {
				return CommutativeIsMatchQ(aExpression.Parts[1:len(aExpression.Parts)], bExpression.Parts[1:len(bExpression.Parts)], pm, cl)
			}
		}
	}

	return NonCommutativeIsMatchQ(aExpression.Parts, bExpression.Parts, pm, cl)
}

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
		aSym, aSymOk := aExpression.Parts[0].(*Symbol)
		otherSym, otherSymOk := bExpression.Parts[0].(*Symbol)
		if aSymOk && otherSymOk {
			if aSym.Name == otherSym.Name {
				if IsOrderless(aSym) {
					return a.IsEqual(b, cl) == "EQUAL_TRUE"
				}
			}
		}

		return FunctionIsSameQ(aExpression.Parts, bExpression.Parts, cl)
	}

	// This should never happen
	return false
}

func (this *Expression) EvalMatchQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	if res, _ := IsMatchQ(this.Parts[1], this.Parts[2], EmptyPD(), &es.CASLogger); res {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}

func GetComparisonDefinitions() (defs []Definition) {
	return
}
