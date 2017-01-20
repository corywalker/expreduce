package expreduce

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

func IsBlankTypeCapturing(e Ex, target Ex, t string, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
	pm = CopyPD(pm)
	asPattern, patternOk := HeadAssertion(e, "Pattern")
	if patternOk {
		asBlank, blankOk := HeadAssertion(asPattern.Parts[2], "Blank")
		asBS, bsOk := HeadAssertion(asPattern.Parts[2], "BlankSequence")
		asBNS, bnsOk := HeadAssertion(asPattern.Parts[2], "BlankNullSequence")
		if blankOk || bsOk || bnsOk {
			parts := []Ex{}
			if blankOk {
				parts = asBlank.Parts
			} else if bsOk {
				parts = asBS.Parts
			} else if bnsOk {
				parts = asBNS.Parts
			}
			//if len(parts) < 2 {
			//return true, pm
			//}
			cl.Debugf("%v %v", parts, len(parts))
			matchesHead := false
			if len(parts) < 2 {
				matchesHead = true
			} else {
				asSymbol, symbolOk := parts[1].(*Symbol)
				if symbolOk {
					if asSymbol.Name == t {
						matchesHead = true
					}
				}
			}
			cl.Debugf("%v", matchesHead)
			if matchesHead {
				sAsSymbol, sAsSymbolOk := asPattern.Parts[1].(*Symbol)
				if sAsSymbolOk {
					// TODO: we should handle matches with BlankSequences
					// differently here.
					//_, isd := es.defined[sAsSymbol.Name]
					toMatch, ispd := pm.patternDefined[sAsSymbol.Name]
					if !ispd {
						toMatch = target
						pm.patternDefined[sAsSymbol.Name] = target
					}
					if !IsSameQ(toMatch, target, cl) {
						return false, pm
					}

					/*if !isd {
						//es.defined[sAsSymbol.Name] = target
						es.Define(sAsSymbol.Name, sAsSymbol, target)
					} else {
						//return es.defined[sAsSymbol.Name].IsSameQ(target, es)
						return true
					}*/
				}
				return true, pm
			}
			return false, pm
		}
	}
	asBlank, blankOk := HeadAssertion(e, "Blank")
	asBS, bsOk := HeadAssertion(e, "BlankSequence")
	asBNS, bnsOk := HeadAssertion(e, "BlankNullSequence")
	if blankOk || bsOk || bnsOk {
		var asSymbol *Symbol
		parts := []Ex{}
		if blankOk {
			parts = asBlank.Parts
		} else if bsOk {
			parts = asBS.Parts
		} else if bnsOk {
			parts = asBNS.Parts
		}
		if len(parts) < 2 {
			return true, pm
		}
		asSymbol, symbolOk := parts[1].(*Symbol)
		if symbolOk {
			return asSymbol.Name == t, pm
		}
	}
	return false, pm
}

func BlankNullSequenceToBlank(bns *Expression) *Expression {
	if len(bns.Parts) < 2 {
		return &Expression{[]Ex{&Symbol{"Blank"}}}
	}
	return &Expression{[]Ex{&Symbol{"Blank"}, bns.Parts[1]}}
}

func BlankSequenceToBlank(bs *Expression) *Expression {
	if len(bs.Parts) < 2 {
		return &Expression{[]Ex{&Symbol{"Blank"}}}
	}
	return &Expression{[]Ex{&Symbol{"Blank"}, bs.Parts[1]}}
}
