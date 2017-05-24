package expreduce

// TODO: do not export this
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
	// Special case for Alternatives
	alts, isAlts := HeadAssertion(b, "Alternatives")
	if isAlts {
		for _, alt := range alts.Parts[1:] {
			// I recently changed the third argument from EmptyPD() to pm
			// because MatchQ[{a, b}, {a_, k | a_}] was returning True, causing
			// problems in some of the boolean patterns. Might need to make
			// similar changes to the other pattern clauses.
			matchq, newPD := IsMatchQ(a, alt, pm, cl)
			if matchq {
				return matchq, newPD
			}
		}
		return false, pm
	}
	// Special case for PatternTest
	patternTest, isPT := HeadAssertion(b, "PatternTest")
	if isPT {
		if len(patternTest.Parts) == 3 {
			matchq, newPD := IsMatchQ(a, patternTest.Parts[1], EmptyPD(), cl)
			if matchq {
				tmpEs := NewEvalStateNoLog(true)
				res := (NewExpression([]Ex{
					patternTest.Parts[2],
					a,
				})).Eval(tmpEs)
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
				tmpEs := NewEvalStateNoLog(true)
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
		return isMatchQRational(aRational, bExpression, pm, cl)
	} else if aIsExpression && bIsRational {
		return isMatchQRational(bRational, aExpression, pm, cl)
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
				return OrderlessIsMatchQ(aExpression.Parts[1:len(aExpression.Parts)], bExpression.Parts[1:len(bExpression.Parts)], pm, cl)
			}
		}
	}

	return NonOrderlessIsMatchQ(aExpression.Parts, bExpression.Parts, pm, cl)
}

func isMatchQRational(a *Rational, b *Expression, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	return IsMatchQ(
		NewExpression([]Ex{
			&Symbol{"Rational"},
			&Integer{a.Num},
			&Integer{a.Den},
		}),

		b, pm, cl)
}

// Should a MatchQ call do:
// 1. Modify pm directly <- bad idea. If we attempt a match and it partially
//    matches, we'll have to restore pm from a snapshot
// 2. Return a modified pm <- probably simplest
// 3. Return a pm with fields to add <- would be most efficient, but complicated
//    and could easily be incorrectly used.
// See IsBlankCapturing for a good example of good use.
func OrderlessIsMatchQ(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	pm = CopyPD(pm)
	if cl.debugState {
		cl.Debugf("Entering OrderlessIsMatchQ(components: %s, lhs_components: %s, pm: %s)", ExArrayToString(components), ExArrayToString(lhs_components), pm)
	}
	nonBS, bs := extractBlankSequences(lhs_components)
	// This is because MatchQ[a + b + c, b + c] == False. We should be careful
	// though because MatchQ[a + b + c, c + __] == True.
	if len(bs) == 0 && len(components) != len(lhs_components) {
		cl.Debugf("len(components) != len(lhs_components). OrderlessMatchQ failed")
		return false, pm
	} else if len(nonBS) > len(components) {
		cl.Debugf("len(nonBS) > len(components). OrderlessMatchQ failed")
		return false, pm
	}

	// After determining that there is a blanksequence, I should go through
	// Each element of the pattern to be matched to see if it even exists within
	// components. I should use MemberQ for this. This can avoid the time-
	// consuming algorithms below

	// These lines are causing MatchQ[a + b, a + b + x___Plus] == True to fail
	for _, mustContain := range lhs_components {
		if !MemberQ(components, mustContain, cl) {
			return false, pm
		}
	}

	kConstant := len(components)
	if len(bs) == 1 {
		// This is probably the most common case. It would be rare for us to
		// have multiple BlankSequences in the same LHS. It saves us a lot of
		// time by doing this
		kConstant = len(nonBS)
	}

	// Start iterating through each permutation of LHS expressions
	perm, cont := make([]int, len(components)), 1
	for i := range perm {
		perm[i] = i
	}
	// Order lhs_components because if we have len(bs) == 1, we will depend on
	// the last n-k items to be orderless. This means that the BlankSequence
	// must be at the end. Eventually this may not be needed once automatic
	// sorting is implemented
	ordered_lhs_components := append(nonBS, bs...)
	for cont == 1 {
		cl.Debugf("Using perm: %v\n", perm)

		// Build a version of components with the correct order. Can I do this
		// more efficiently with a slice notation? Let's copy for now.
		orderedComponents := make([]Ex, len(components))
		for oci, ci := range perm {
			orderedComponents[oci] = components[ci].DeepCopy()
		}
		if cl.debugState {
			cl.Debugf("%s", ExArrayToString(orderedComponents))
		}
		ncIsMatchQ, newPm := NonOrderlessIsMatchQ(orderedComponents, ordered_lhs_components, pm, cl)
		if ncIsMatchQ {
			cl.Debugf("OrderlessIsMatchQ succeeded. Context: %s", pm)
			return true, newPm
		}

		// Generate next permutation, if any
		cont = nextKPermutation(perm, len(components), kConstant)
	}
	cl.Debugf("OrderlessIsMatchQ failed. Context: %s", pm)
	return false, pm
}

func NonOrderlessIsMatchQ(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	pm = CopyPD(pm)
	// This function is now recursive because of the existence of BlankSequence.
	if cl.debugState {
		cl.Debugf("Entering NonOrderlessIsMatchQ(components: %s, lhs_components: %s, pm: %s)", ExArrayToString(components), ExArrayToString(lhs_components), pm)
	}
	// A base case for the recursion
	if len(components) == 0 && len(lhs_components) == 0 {
		return true, pm
	}
	if len(components) != 0 && len(lhs_components) == 0 {
		return false, pm
	}

	progressI := 0
	for i := 0; i < Max(len(components), len(lhs_components)); i++ {
		progressI = i
		if i >= len(lhs_components) {
			return false, pm
		}
		if i >= len(components) {
			cl.Debugf("Checking if IsMatchQ(INDEX_ERROR, %s). i=%d, Current context: %v\n", lhs_components[i], i, pm)
		} else {
			cl.Debugf("Checking if IsMatchQ(%s, %s). i=%d, Current context: %v\n", components[i], lhs_components[i], i, pm)
		}
		pat, isPat := HeadAssertion(lhs_components[i], "Pattern")
		bns, isBns := HeadAssertion(lhs_components[i], "BlankNullSequence")
		bs, isBs := HeadAssertion(lhs_components[i], "BlankSequence")
		if isPat {
			bns, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
			bs, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		}
		if isBns || isBs {
			cl.Debugf("Encountered BS or BNS!")
			remainingLhs := make([]Ex, len(lhs_components)-i-1)
			for k := i + 1; k < len(lhs_components); k++ {
				remainingLhs[k-i-1] = lhs_components[k].DeepCopy()
			}
			startI := 0
			if isBns {
				startI = i - 1
			} else {
				startI = i
			}
			for j := startI; j < len(components); j++ {
				// This process involves a lot of extraneous copying. I should
				// test to see how much of these arrays need to be copied from
				// scratch on every iteration.
				seqToTry := make([]Ex, j-i+1)
				for k := i; k <= j; k++ {
					seqToTry[k-i] = components[k].DeepCopy()
				}
				seqMatches := false
				if isBns {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankNullSequenceToBlank(bns), cl)
				} else {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankSequenceToBlank(bs), cl)
				}
				cl.Debugf("%v", seqMatches)
				remainingComps := make([]Ex, len(components)-j-1)
				for k := j + 1; k < len(components); k++ {
					remainingComps[k-j-1] = components[k].DeepCopy()
				}
				if cl.debugState {
					cl.Debugf("%d %s %s %s", j, ExArrayToString(seqToTry), ExArrayToString(remainingComps), ExArrayToString(remainingLhs))
				}
				matchq, newPDs := NonOrderlessIsMatchQ(remainingComps, remainingLhs, pm, cl)
				if seqMatches && matchq {
					pm.Update(newPDs)
					if isPat {
						sAsSymbol, sAsSymbolOk := pat.Parts[1].(*Symbol)
						if sAsSymbolOk {
							toTryParts := []Ex{&Symbol{"Sequence"}}
							toTryParts = append(toTryParts, seqToTry...)
							target := NewExpression(toTryParts)
							_, ispd := pm.patternDefined[sAsSymbol.Name]
							if !ispd {
								pm.patternDefined[sAsSymbol.Name] = target
							}
							if !IsSameQ(pm.patternDefined[sAsSymbol.Name], target, cl) {
								return false, pm
							}
						}
					}
					return true, pm
				}
			}
			return false, pm
		}
		if i >= len(components) {
			return false, pm
		}
		ismatchq, toAdd := IsMatchQ(components[i].DeepCopy(), lhs_components[i], pm, cl)
		if ismatchq {
			cl.Debugf("Returned True!\n")
			pm.Update(toAdd)
		} else {
			cl.Debugf("NonOrderlessIsMatchQ failed. Context: %s", pm)
			return false, pm
		}
	}
	if progressI == len(lhs_components)-1 {
		return true, pm
	} else {
		return false, pm
	}
}

func extractBlankSequences(components []Ex) (nonBS []Ex, bs []Ex) {
	for _, c := range components {
		pat, isPat := HeadAssertion(c, "Pattern")
		_, isBns := HeadAssertion(c, "BlankNullSequence")
		_, isBs := HeadAssertion(c, "BlankSequence")
		if isPat {
			_, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
			_, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		}
		if isBs || isBns {
			bs = append(bs, c)
		} else {
			nonBS = append(nonBS, c)
		}
	}
	return
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
