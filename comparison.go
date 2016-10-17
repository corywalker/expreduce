package cas

import "bytes"

func (this *Expression) EvalEqual(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var isequal string = this.Parts[1].Eval(es).IsEqual(this.Parts[2].Eval(es), &es.CASLogger)
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

	var issame bool = IsSameQ(this.Parts[1].Eval(es), this.Parts[2].Eval(es), &es.CASLogger)
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

func IsMatchQ(a Ex, b Ex, es *EvalState) bool {
	_, aIsFlt := a.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, aIsString := a.(*String)
	_, aIsSymbol := a.(*Symbol)
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
	}

	if IsBlankTypeOnly(b) {
		if IsBlankTypeCapturing(b, a, headStr, es) {
			return true
		}
		return false
	}
	if aIsFlt || aIsInteger || aIsString || aIsSymbol {
		return IsSameQ(a, b, &es.CASLogger)
	}

	if !(aIsExpression && bIsExpression) {
		return false
	}

	aExpressionSym, aExpressionSymOk := aExpression.Parts[0].(*Symbol)
	bExpressionSym, bExpressionSymOk := bExpression.Parts[0].(*Symbol)
	if aExpressionSymOk && bExpressionSymOk {
		if aExpressionSym.Name == bExpressionSym.Name {
			if IsOrderless(aExpressionSym) {
				return CommutativeIsMatchQ(aExpression.Parts[1:len(aExpression.Parts)], bExpression.Parts[1:len(bExpression.Parts)], es)
			}
		}
	}

	return NonCommutativeIsMatchQ(aExpression.Parts, bExpression.Parts, es)
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
	aExpression, aIsExpression := a.(*Expression)
	bExpression, bIsExpression := b.(*Expression)

	if (aIsFlt && bIsFlt) || (aIsString && bIsString) || (aIsInteger && bIsInteger) || (aIsSymbol && bIsSymbol) {

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
func IsMatchQClearDefs(a Ex, b Ex, es *EvalState) bool {
	oldVars := es.GetDefinedSnapshot()
	isSame := IsMatchQ(a, b, es)
	es.ClearPD()
	es.defined = oldVars
	return isSame
}

func (this *Expression) EvalMatchQ(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	if IsMatchQClearDefs(this.Parts[1], this.Parts[2], es) {
		return &Symbol{"True"}
	} else {
		return &Symbol{"False"}
	}
}
