package cas

import "bytes"

func (this *Expression) ToStringPattern() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Pattern[")
		buffer.WriteString(this.Parts[1].String())
		buffer.WriteString(", ")
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Parts[2].String())
		buffer.WriteString("]")
	} else {
		buffer.WriteString(this.Parts[1].String())
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Parts[2].String())
	}
	return buffer.String()
}

func (this *Expression) ToStringBlank() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Blank[")
		buffer.WriteString(this.Parts[1].String())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("_")
		buffer.WriteString(this.Parts[1].String())
	}
	return buffer.String()
}

func (this *Expression) ToStringBlankSequence() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankSequence[")
		buffer.WriteString(this.Parts[1].String())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("__")
		buffer.WriteString(this.Parts[1].String())
	}
	return buffer.String()
}

func (this *Expression) ToStringBlankNullSequence() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankNullSequence[")
		buffer.WriteString(this.Parts[1].String())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("___")
		buffer.WriteString(this.Parts[1].String())
	}
	return buffer.String()
}

// -------------------------

func IsBlankTypeOnly(e Ex) bool {
	asPattern, patternOk := HeadAssertion(e, "Pattern")
	if patternOk {
		_, blankOk := HeadAssertion(asPattern.Parts[2], "Blank")
		_, bsOk := HeadAssertion(asPattern.Parts[2], "BlankSequence")
		_, bnsOk := HeadAssertion(asPattern.Parts[2], "BlankNullSequence")
		if blankOk || bsOk || bnsOk {
			return true
		}
	}
	_, blankOk := HeadAssertion(e, "Blank")
	_, bsOk := HeadAssertion(e, "BlankSequence")
	_, bnsOk := HeadAssertion(e, "BlankNullSequence")
	if blankOk || bsOk || bnsOk {
		return true
	}
	return false
}

func IsBlankType(e Ex, t string) bool {
	// Calling this function on an amatch_Integer with t == "Integer" would
	// yield true, while calling this function on an actual integer with
	// t == "Integer" would return false.
	asPattern, patternOk := HeadAssertion(e, "Pattern")
	if patternOk {
		asBlank, blankOk := HeadAssertion(asPattern.Parts[2], "Blank")
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

func IsBlankTypeCapturing(e Ex, target Ex, t string, pm *PDManager, cl *CASLogger) (bool, map[string]Ex) {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
	newPDs := make(map[string]Ex)
	asPattern, patternOk := HeadAssertion(e, "Pattern")
	if patternOk {
		asBlank, blankOk := HeadAssertion(asPattern.Parts[2], "Blank")
		asBS, bsOk := HeadAssertion(asPattern.Parts[2], "BlankSequence")
		asBNS, bnsOk := HeadAssertion(asPattern.Parts[2], "BlankNullSequence")
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
					sAsSymbol, sAsSymbolOk := asPattern.Parts[1].(*Symbol)
					if sAsSymbolOk {
						// TODO: we should handle matches with BlankSequences
						// differently here.
						//_, isd := es.defined[sAsSymbol.Name]
						toMatch, ispd := pm.patternDefined[sAsSymbol.Name]
						if !ispd {
							toMatch = target
							newPDs[sAsSymbol.Name] = target
						}
						if !IsSameQ(toMatch, target, cl) {
							return false, newPDs
						}

						/*if !isd {
							//es.defined[sAsSymbol.Name] = target
							es.Define(sAsSymbol.Name, sAsSymbol, target)
						} else {
							//return es.defined[sAsSymbol.Name].IsSameQ(target, es)
							return true
						}*/
					}
					return true, newPDs
				}
				return false, newPDs
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
			return asSymbol.Name == t || asSymbol.Name == "", newPDs
		}
	}
	return false, newPDs
}

func BlankNullSequenceToBlank(bns *Expression) *Expression {
	return &Expression{[]Ex{&Symbol{"Blank"}, bns.Parts[1]}}
}

func BlankSequenceToBlank(bs *Expression) *Expression {
	return &Expression{[]Ex{&Symbol{"Blank"}, bs.Parts[1]}}
}

func ExArrayTestRepeatingMatch(array []Ex, blank *Expression, cl *CASLogger) bool {
	toReturn := true
	for _, e := range array {
		tmpEs := NewEvalStateNoLog()
		isMatch, _ := IsMatchQ(e, blank, &tmpEs.PDManager, &tmpEs.CASLogger)
		cl.Debugf("%v %v %v", e, blank, isMatch)
		toReturn = toReturn && isMatch
	}
	return toReturn
}
