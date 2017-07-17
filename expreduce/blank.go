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

func IsBlankTypeCapturing(e Ex, target Ex, head Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
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
				matchesHead = IsSameQ(head, parts[1], cl)
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
		return IsSameQ(head, parts[1], cl), pm
	}
	return false, pm
}

func BlankNullSequenceToBlank(bns *Expression) *Expression {
	if len(bns.Parts) < 2 {
		return NewExpression([]Ex{&Symbol{"Blank"}})
	}
	return NewExpression([]Ex{&Symbol{"Blank"}, bns.Parts[1]})
}

func BlankSequenceToBlank(bs *Expression) *Expression {
	if len(bs.Parts) < 2 {
		return NewExpression([]Ex{&Symbol{"Blank"}})
	}
	return NewExpression([]Ex{&Symbol{"Blank"}, bs.Parts[1]})
}
