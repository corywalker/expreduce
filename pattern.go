package cas

import "bytes"

func ToStringBlankType(repr string, parts []Ex, form string) (bool, string) {
	if form == "FullForm" {
		return false, ""
	}
	if len(parts) == 1 {
		return true, repr
	} else if len(parts) == 2 {
		var buffer bytes.Buffer
		buffer.WriteString(repr)
		buffer.WriteString(parts[1].String())
		return true, buffer.String()
	}
	return false, ""
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

func ExArrayTestRepeatingMatch(array []Ex, blank *Expression, cl *CASLogger) bool {
	toReturn := true
	for _, e := range array {
		tmpEs := NewEvalStateNoLog(false)
		isMatch, _ := IsMatchQ(e, blank, EmptyPD(), &tmpEs.CASLogger)
		cl.Debugf("%v %v %v", e, blank, isMatch)
		toReturn = toReturn && isMatch
	}
	return toReturn
}

func GetPatternDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Pattern",
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			if form != "InputForm" && form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			buffer.WriteString(this.Parts[1].StringForm(form))
			buffer.WriteString(this.Parts[2].StringForm(form))
			return true, buffer.String()
		},
	})
	defs = append(defs, Definition{
		name: "Blank",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("_", this.Parts, form)
		},
		tests: []TestInstruction{
			// Matching patterns
			&SameTest{"True", "MatchQ[1, _Integer]"},
			&SameTest{"False", "MatchQ[s, _Integer]"},
			&SameTest{"True", "MatchQ[s, _Symbol]"},
			&SameTest{"False", "MatchQ[1, _Symbol]"},
			&SameTest{"False", "MatchQ[_Symbol, _Symbol]"},
			&SameTest{"False", "MatchQ[_Integer, _Integer]"},
			&SameTest{"True", "MatchQ[_Symbol, _Blank]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"False", "MatchQ[_Symbol, test_Symbol]"},
			&SameTest{"False", "MatchQ[name_Symbol, test_Blank]"},
			&SameTest{"True", "MatchQ[name_Symbol, test_Pattern]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"False", "MatchQ[_Symbol, test_Pattern]"},
			&SameTest{"False", "MatchQ[1.5, _Integer]"},
			&SameTest{"True", "MatchQ[1.5, _Real]"},
			&SameTest{"True", "_Symbol == _Symbol"},
			&SameTest{"_Symbol == _Integer", "_Symbol == _Integer"},
			&SameTest{"False", "MatchQ[_Symbol, s]"},
			&SameTest{"False", "MatchQ[_Integer, 1]"},
			&SameTest{"_Integer == 1", "_Integer == 1"},
			&SameTest{"1 == _Integer", "1 == _Integer"},

			&SameTest{"False", "_Integer === 1"},
			&SameTest{"False", "1 === _Integer"},
			&SameTest{"True", "_Integer === _Integer"},
			&SameTest{"False", "_Symbol === a"},
			&SameTest{"False", "a === _Symbol"},
			&SameTest{"True", "_Symbol === _Symbol"},

			&SameTest{"a == b", "a == b"},
			&SameTest{"2", "a == b /. _Equal -> 2"},
			&SameTest{"If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]"},
			&SameTest{"99", "If[1 == k, itstrue, itsfalse] /. _If -> 99"},
			&SameTest{"False", "MatchQ[kfdsfdsf[], _Function]"},
			&SameTest{"True", "MatchQ[kfdsfdsf[], _kfdsfdsf]"},
			&SameTest{"99", "kfdsfdsf[] /. _kfdsfdsf -> 99"},
			&SameTest{"a + b", "a + b"},
			&SameTest{"2", "a + b /. _Plus -> 2"},
			&SameTest{"2", "a*b /. _Times -> 2"},
			&SameTest{"2", "a^b /. _Power -> 2"},
			&SameTest{"2", "a -> b /. _Rule -> 2"},
			&SameTest{"2", "a*b*c*d /. _Times -> 2"},

			&SameTest{"True", "MatchQ[x*3., c1match_Real*matcha_]"},
			&SameTest{"True", "MatchQ[3.*x, c1match_Real*matcha_]"},
			&SameTest{"True", "MatchQ[x+3., c1match_Real+matcha_]"},
			&SameTest{"True", "MatchQ[3.+x, c1match_Real+matcha_]"},
			&SameTest{"True", "MatchQ[y + x, matcha_]"},
			&SameTest{"True", "MatchQ[y*x, matcha_]"},
		},
	})
	defs = append(defs, Definition{
		name: "BlankSequence",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("__", this.Parts, form)
		},
		tests: []TestInstruction{
			// Be wary of the false matches - the default is usually false.
			&SameTest{"True", "MatchQ[a, __]"},
			&SameTest{"True", "MatchQ[a + b, __]"},
			&SameTest{"True", "MatchQ[a*b, __]"},
			&SameTest{"False", "MatchQ[a, a*__]"},
			&SameTest{"True", "MatchQ[a + b + c, a + b + __]"},
			&SameTest{"True", "MatchQ[a + b + c + d, a + b + __]"},
			&SameTest{"False", "MatchQ[a*b, __Symbol]"},
			&SameTest{"False", "MatchQ[a*b, x__Symbol]"},
			&SameTest{"True", "MatchQ[a, __Symbol]"},
			&SameTest{"True", "MatchQ[a*b, x__Times]"},
			&SameTest{"False", "MatchQ[a*b, x__Plus]"},
			&SameTest{"True", "MatchQ[a + b, x__Plus]"},
			&SameTest{"True", "MatchQ[a + b + c, a + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b + c, a + x__Plus]"},
			&SameTest{"True", "MatchQ[a + b, a + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b, a + x__Plus]"},
			&SameTest{"False", "MatchQ[a + b, a + b + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b, a + b + x__Plus]"},
			&SameTest{"True", "MatchQ[4*a*b*c*d*e*f, __]"},
			&SameTest{"True", "MatchQ[4*a*b*c*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[4*a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[4*a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f, 5*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__ + 5*k]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 2 + 5*k, 4*__ + 5*k]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e, __^e]"},
			&SameTest{"False", "MatchQ[(a*b*c)^e, __^f + __^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a*b*c)^f, __^f + __^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a + b + c)^f, __^f + __^e]"},
			&SameTest{"False", "MatchQ[(a*b*c)^e + (a + b + c)^f, amatch__^f + amatch__^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a*b*c)^f, amatch__^f + amatch__^e]"},

			// Warm up for combining like terms
			&SameTest{"True", "MatchQ[bar[1, foo[a, b]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"True", "MatchQ[bar[1, foo[a, b, c]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"False", "MatchQ[bar[1, foo[]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"2", "bar[1, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2"},
			&SameTest{"4", "bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2"},
			&SameTest{"6 * buzz[a, b]", "bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> amatch*buzz[cmatch]"},
			&SameTest{"bar[3, foo[a, b]]", "bar[1, foo[a, b]] + bar[2, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] + bar[bmatch_Integer, foo[cmatch__]] -> bar[amatch + bmatch, foo[cmatch]]"},

			// Test special case of Orderless sequence matches
			&SameTest{"Null", "fooPlus[Plus[addends__]] := Hold[addends]"},
			&SameTest{"Null", "fooList[List[addends__]] := Hold[addends]"},
			&SameTest{"Null", "fooBlank[_[addends__]] := Hold[addends]"},
			&SameTest{"Hold[a, b, c]", "fooList[List[a, b, c]]"},
			&SameTest{"Hold[a, b, c]", "fooBlank[Plus[a, b, c]]"},

			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[__]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[__Real]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[__Real]]"},
			&SameTest{"False", "MatchQ[foo[], foo[__Real]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[__]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, ___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, ___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, ___Integer, 3]]"},

			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 5]]"},
		},
	})
	defs = append(defs, Definition{
		name: "BlankNullSequence",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("___", this.Parts, form)
		},
		tests: []TestInstruction{
			&SameTest{"True", "MatchQ[a*b, ___]"},
			&SameTest{"False", "MatchQ[a, a*___]"},
			&SameTest{"False", "MatchQ[a, a + ___]"},
			&SameTest{"True", "MatchQ[a + b, a + b + ___]"},
			&SameTest{"False", "MatchQ[a*b, ___Integer]"},
			&SameTest{"False", "MatchQ[a*b, ___Symbol]"},
			&SameTest{"True", "MatchQ[a, ___Symbol]"},
			&SameTest{"False", "MatchQ[a + b, ___Symbol]"},
			&SameTest{"True", "MatchQ[a + b + c, a + x___Symbol]"},
			&SameTest{"False", "MatchQ[a + b + c, a + x___Plus]"},
			&SameTest{"True", "MatchQ[a + b, a + b + x___Symbol]"},

			&SameTest{"True", "MatchQ[foo[1.], foo[___]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[___Real]]"},
			&SameTest{"False", "MatchQ[foo[1.], foo[___Integer]]"},
			&SameTest{"True", "MatchQ[foo[], foo[___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2]]"},
			&SameTest{"False", "MatchQ[foo[1, 2], foo[1, 2, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 5]]"},

			// Make sure some similar cases still work with Patterns, not just Blanks
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, a___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a___Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3, 4], foo[1, a__Integer, 3, b___Integer, 4]]"},
		},
	})
	defs = append(defs, Definition{
		name: "Except",
		tests: []TestInstruction{
			&SameTest{"{5, 2, x, y, 4}", "Cases[{5, 2, 3.5, x, y, 4}, Except[_Real]]"},
			&SameTest{"{5, 2, x, y, 4}", "Cases[{5, 2, a^b, x, y, 4}, Except[_Symbol^_Symbol]]"},
			&SameTest{"{a, b, 0, foo[1], foo[2], x, y}", "{a, b, 0, 1, 2, x, y} /. Except[0, a_Integer] -> foo[a]"},
		},
	})
	defs = append(defs, Definition{
		name: "PatternTest",
		tests: []TestInstruction{
			&SameTest{"True", "MatchQ[1, _?NumberQ]"},
			&SameTest{"False", "MatchQ[a, _?NumberQ]"},
			&SameTest{"True", "MatchQ[1, 1?NumberQ]"},
			&SameTest{"False", "MatchQ[1, 1.5?NumberQ]"},
			&SameTest{"True", "MatchQ[1.5, 1.5?NumberQ]"},
			&SameTest{"{5,2,4.5}", "Cases[{5, 2, a^b, x, y, 4.5}, _?NumberQ]"},
		},
	})
	defs = append(defs, Definition{
		name: "Condition",
		tests: []TestInstruction{
			&SameTest{"True", "MatchQ[5, _ /; True]"},
			&SameTest{"False", "MatchQ[5, _ /; False]"},
			&SameTest{"True", "MatchQ[5, y_ /; True]"},
			&SameTest{"False", "MatchQ[5, y_Real /; True]"},
			&SameTest{"True", "MatchQ[5, y_Integer /; True]"},
			&SameTest{"False", "MatchQ[5, y_ /; y == 0]"},
			&SameTest{"True", "MatchQ[5, y_ /; y == 5]"},
			//&SameTest{"{1,2,3,5}", "{3, 5, 2, 1} //. {x___, y_, z_, k___} /; (Order[y, z] == -1) -> {x, z, y, k}"},
		},
	})
	defs = append(defs, Definition{
		name: "Alternatives",
		tests: []TestInstruction{
			&SameTest{"Alternatives[c,d]", "c | d"},
			&SameTest{"False", "MatchQ[b, c | d]"},
			&SameTest{"True", "MatchQ[c, c | d]"},
			&SameTest{"True", "MatchQ[d, c | d]"},
			&SameTest{"{c, 1, 2}", "Cases[{a, b, c, 1, 2}, c | _Integer]"},
			&SameTest{"(1 + List)[1 + a, 1 + b, 1 + c, 1., 3]", "{a, b, c, 1., 2} /. amatch_Symbol | amatch_Integer -> amatch + 1"},
			&SameTest{"{b, c, d, e}", "Cases[{a, b, c, d, e, f}, b | c | d | e]"},
		},
	})
	return
}
