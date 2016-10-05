package cas

import "bytes"

type Pattern struct {
	S   Ex
	Obj Ex
}

func (this *Pattern) Eval(es *EvalState) Ex {
	return this
}

func (this *Pattern) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.S = this.S.Replace(r, es)
	this.Obj = this.Obj.Replace(r, es)
	return this.Eval(es)
}

func (this *Pattern) ToString() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Pattern[")
		buffer.WriteString(this.S.ToString())
		buffer.WriteString(", ")
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Obj.ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString(this.S.ToString())
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Obj.ToString())
	}
	return buffer.String()
}

func (this *Pattern) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Pattern)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.S,
		this.Obj,
	}, []Ex{
		other.S,
		other.Obj,
	}, es)
}

func (this *Pattern) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Pattern)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.S,
		this.Obj,
	}, []Ex{
		other.S,
		other.Obj,
	}, es)
}

func IsBlankType(e Ex, t string) bool {
	// Calling this function on an amatch_Integer with t == "Integer" would
	// yield true, while calling this function on an actual integer with
	// t == "Integer" would return false.
	asPattern, patternOk := e.(*Pattern)
	if patternOk {
		asBlank, blankOk := HeadAssertion(asPattern.Obj, "Blank")
		if blankOk {
			asSymbol, symbolOk := asBlank.Parts[1].(*Symbol)
			if symbolOk {
				return asSymbol.Name == t
			}
		}
	}
	asBlank, blankOk := HeadAssertion(e, "Blank")
	if blankOk {
		asSymbol, symbolOk := asBlank.Parts[1].(*Symbol)
		if symbolOk {
			return asSymbol.Name == t
		}
	}
	// TODO: Should I add BlankSequence support here? Doesn't seem to impact
	// tests.
	return false
}

func IsBlankTypeCapturing(e Ex, target Ex, t string, es *EvalState) bool {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
	asPattern, patternOk := e.(*Pattern)
	if patternOk {
		asBlank, blankOk := HeadAssertion(asPattern.Obj, "Blank")
		asBS, bsOk := HeadAssertion(asPattern.Obj, "BlankSequence")
		asBNS, bnsOk := HeadAssertion(asPattern.Obj, "BlankNullSequence")
		if blankOk || bsOk || bnsOk {
			var asSymbol *Symbol
			symbolOk := false
			if blankOk {
				asSymbol, symbolOk = asBlank.Parts[1].(*Symbol)
			} else if bsOk {
				asSymbol, symbolOk = asBS.Parts[1].(*Symbol)
			} else if bnsOk {
				asSymbol, symbolOk = asBNS.Parts[1].(*Symbol)
			}
			if symbolOk {
				if asSymbol.Name == t || asSymbol.Name == "" {
					sAsSymbol, sAsSymbolOk := asPattern.S.(*Symbol)
					if sAsSymbolOk {
						// TODO: we should handle matches with BlankSequences
						// differently here.
						_, isd := es.defined[sAsSymbol.Name]
						_, ispd := es.patternDefined[sAsSymbol.Name]
						if !ispd {
							es.patternDefined[sAsSymbol.Name] = target
						}
						if !es.patternDefined[sAsSymbol.Name].IsSameQ(target, es) {
							return false
						}

						if !isd {
							//es.defined[sAsSymbol.Name] = target
							es.Define(sAsSymbol.Name, sAsSymbol, target)
						} else {
							//return es.defined[sAsSymbol.Name].IsSameQ(target, es)
							return true
						}
					}
					return true
				}
				return false
			}
		}
	}
	asBlank, blankOk := HeadAssertion(e, "Blank")
	asBS, bsOk := HeadAssertion(e, "BlankSequence")
	asBNS, bnsOk := HeadAssertion(e, "BlankNullSequence")
	if blankOk || bsOk || bnsOk {
		var asSymbol *Symbol
		symbolOk := false
		if blankOk {
			asSymbol, symbolOk = asBlank.Parts[1].(*Symbol)
		} else if bsOk {
			asSymbol, symbolOk = asBS.Parts[1].(*Symbol)
		} else if bnsOk {
			asSymbol, symbolOk = asBNS.Parts[1].(*Symbol)
		}
		if symbolOk {
			return asSymbol.Name == t || asSymbol.Name == ""
		}
	}
	return false
}

func (this *Pattern) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Pattern") {
		return true
	}
	//return this.IsSameQ(otherEx, es)
	return false
}

func (this *Pattern) DeepCopy() Ex {
	return &Pattern{
		this.S.DeepCopy(),
		this.Obj.DeepCopy(),
	}
}

func (this *Expression) ToStringBlank() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Blank[")
		buffer.WriteString(this.Parts[1].ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("_")
		buffer.WriteString(this.Parts[1].ToString())
	}
	return buffer.String()
}

func (this *Expression) ToStringBlankSequence() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankSequence[")
		buffer.WriteString(this.Parts[1].ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("__")
		buffer.WriteString(this.Parts[1].ToString())
	}
	return buffer.String()
}

func (this *Expression) ToStringBlankNullSequence() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankNullSequence[")
		buffer.WriteString(this.Parts[1].ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("___")
		buffer.WriteString(this.Parts[1].ToString())
	}
	return buffer.String()
}

// -------------------------

func BlankNullSequenceToBlank(bns *Expression) *Expression {
	return &Expression{[]Ex{&Symbol{"Blank"}, bns.Parts[1]}}
}

func BlankSequenceToBlank(bs *Expression) *Expression {
	return &Expression{[]Ex{&Symbol{"Blank"}, bs.Parts[1]}}
}

func ExArrayTestRepeatingMatch(array []Ex, blank *Expression, es *EvalState) bool {
	toReturn := true
	for _, e := range array {
		tmpEs := NewEvalStateNoLog()
		isMatch := e.IsMatchQ(blank, tmpEs)
		es.log.Debug(e.ToString(), blank.ToString(), isMatch)
		toReturn = toReturn && isMatch
	}
	return toReturn
}
