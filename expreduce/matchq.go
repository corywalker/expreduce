package expreduce

type matchIter interface {
	reset()
	// returns ismatch, pd, isdone
	next() (bool, *PDManager, bool)
}

type dummyMatchIter struct {
	isMatchQ	bool
	pm			*PDManager
	isDone		bool
}

func (this *dummyMatchIter) next() (bool, *PDManager, bool) {
	return this.isMatchQ, this.pm, this.isDone
}

func (this *dummyMatchIter) reset() {}

func NewMatchIter(a Ex, b Ex, pm *PDManager, cl *CASLogger) (matchIter, bool) {
	// Special case for Except
	except, isExcept := HeadAssertion(b, "Except")
	if isExcept {
		if len(except.Parts) == 2 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), cl)
			return &dummyMatchIter{!matchq, pm, true}, true
		} else if len(except.Parts) == 3 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), cl)
			if !matchq {
				matchqb, newPm := IsMatchQ(a, except.Parts[2], pm, cl)
				return &dummyMatchIter{matchqb, newPm, true}, true
			}
			return &dummyMatchIter{false, pm, true}, true
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
				return &dummyMatchIter{matchq, newPD, true}, true
			}
		}
		return &dummyMatchIter{false, pm, true}, true
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
						return &dummyMatchIter{true, newPD, true}, true
					}
				}
			}
			return &dummyMatchIter{false, pm, true}, true
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
						return &dummyMatchIter{true, newPD, true}, true
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
			return &dummyMatchIter{true, ibtcNewPDs, true}, true
		}
		return &dummyMatchIter{false, EmptyPD(), true}, true
	}

	// Handle special case for matching Rational[a_Integer, b_Integer]
	if aIsRational && bIsExpression {
		matchq, newPm := isMatchQRational(aRational, bExpression, pm, cl)
		return &dummyMatchIter{matchq, newPm, true}, true
	} else if aIsExpression && bIsRational {
		matchq, newPm := isMatchQRational(bRational, aExpression, pm, cl)
		return &dummyMatchIter{matchq, newPm, true}, true
	}

	if aIsFlt || aIsInteger || aIsString || aIsSymbol || aIsRational {
		return &dummyMatchIter{IsSameQ(a, b, cl), EmptyPD(), true}, true
	} else if !(aIsExpression && bIsExpression) {
		return &dummyMatchIter{false, EmptyPD(), true}, true
	}

	aExpressionSym, aExpressionSymOk := aExpression.Parts[0].(*Symbol)
	bExpressionSym, bExpressionSymOk := bExpression.Parts[0].(*Symbol)
	if aExpressionSymOk && bExpressionSymOk {
		if aExpressionSym.Name == bExpressionSym.Name {
			if IsOrderless(aExpressionSym) {
				omi, ok := NewOrderlessMatchIter(aExpression.Parts[1:len(aExpression.Parts)], bExpression.Parts[1:len(bExpression.Parts)], pm, cl)
				if !ok {
					return &dummyMatchIter{false, pm, true}, true
				}
				return omi, true
			}
		}
	}

	nomi, ok := NewNonOrderlessMatchIter(aExpression.Parts, bExpression.Parts, pm, cl)
	if !ok {
		return &dummyMatchIter{false, pm, true}, true
	}
	return nomi, true
}

// TODO: do not export this
func IsMatchQ(a Ex, b Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	mi, ok := NewMatchIter(a, b, pm, cl)
	if !ok {
		return false, pm
	}
	// Return the first match.
	matchq, newPd, _ := mi.next()
	return matchq, newPd
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

type orderlessMatchIter struct {
	components		[]Ex
	lhs_components	[]Ex
	ordered_lhs_components	[]Ex
	pm				*PDManager
	cl				*CASLogger
	kConstant		int
	contval			int
	perm			[]int
}

func NewOrderlessMatchIter(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (matchIter, bool) {
	omi := &orderlessMatchIter{}
	omi.components = components
	omi.lhs_components = lhs_components
	// TODO: is copy needed?
	omi.pm = CopyPD(pm)
	omi.cl = cl

	if cl.debugState {
		cl.Debugf("Entering OrderlessIsMatchQ(components: %s, lhs_components: %s, pm: %s)", ExArrayToString(components), ExArrayToString(lhs_components), pm)
	}
	nonBS, bs := extractBlankSequences(lhs_components)
	// This is because MatchQ[a + b + c, b + c] == False. We should be careful
	// though because MatchQ[a + b + c, c + __] == True.
	if len(bs) == 0 && len(components) != len(lhs_components) {
		cl.Debugf("len(components) != len(lhs_components). OrderlessMatchQ failed")
		return omi, false
	} else if len(nonBS) > len(components) {
		cl.Debugf("len(nonBS) > len(components). OrderlessMatchQ failed")
		return omi, false
	}

	// After determining that there is a blanksequence, I should go through
	// Each element of the pattern to be matched to see if it even exists within
	// components. I should use MemberQ for this. This can avoid the time-
	// consuming algorithms below

	// These lines are causing MatchQ[a + b, a + b + x___Plus] == True to fail
	for _, mustContain := range lhs_components {
		if !MemberQ(components, mustContain, cl) {
			return omi, false
		}
	}

	omi.kConstant = len(components)
	if len(bs) == 1 {
		// This is probably the most common case. It would be rare for us to
		// have multiple BlankSequences in the same LHS. It saves us a lot of
		// time by doing this
		omi.kConstant = len(nonBS)
	}

	// Start iterating through each permutation of LHS expressions
	omi.perm, omi.contval = make([]int, len(components)), 1
	for i := range omi.perm {
		omi.perm[i] = i
	}

	// Order lhs_components because if we have len(bs) == 1, we will depend on
	// the last n-k items to be orderless. This means that the BlankSequence
	// must be at the end. Eventually this may not be needed once automatic
	// sorting is implemented
	omi.ordered_lhs_components = append(nonBS, bs...)

	return omi, true
}

// Should a MatchQ call do:
// 1. Modify pm directly <- bad idea. If we attempt a match and it partially
//    matches, we'll have to restore pm from a snapshot
// 2. Return a modified pm <- probably simplest
// 3. Return a pm with fields to add <- would be most efficient, but complicated
//    and could easily be incorrectly used.
// See IsBlankCapturing for a good example of good use.
// Returns if there is a match and the pm that results. This method can be
// called until there is not a match to find all possible matches. It will
// return false from then on.
func (this *orderlessMatchIter) next() (bool, *PDManager, bool) {
	for this.contval == 1 {
		this.cl.Debugf("Using perm: %v\n", this.perm)

		// Build a version of components with the correct order. Can I do this
		// more efficiently with a slice notation? Let's copy for now.
		orderedComponents := make([]Ex, len(this.components))
		for oci, ci := range this.perm {
			orderedComponents[oci] = this.components[ci].DeepCopy()
		}
		if this.cl.debugState {
			this.cl.Debugf("%s", ExArrayToString(orderedComponents))
		}
		ncIsMatchQ, newPm := NonOrderlessIsMatchQ(orderedComponents, this.ordered_lhs_components, this.pm, this.cl)

		// Generate next permutation, if any
		this.contval = nextKPermutation(this.perm, len(this.components), this.kConstant)
		if ncIsMatchQ {
			if this.cl.debugState {
				this.cl.Infof("OrderlessIsMatchQ(%s, %s) succeeded. New pm: %v", ExArrayToString(this.components), ExArrayToString(this.lhs_components), newPm)
			}
			return true, newPm, false
		}
	}
	this.cl.Debugf("OrderlessIsMatchQ failed. Context: %s", this.pm)
	return false, this.pm, true
}

func (this *orderlessMatchIter) reset() {}

func OrderlessIsMatchQ(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	omi, ok := NewOrderlessMatchIter(components, lhs_components, pm, cl)
	if !ok {
		return false, pm
	}
	// Return the first match.
	isMatch, newPm, _ := omi.next()
	return isMatch, newPm
}

type nonOrderlessMatchIter struct {
	components		[]Ex
	lhs_components	[]Ex
	pm				*PDManager
	cl				*CASLogger
	progressI		int
}

func NewNonOrderlessMatchIter(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (matchIter, bool) {
	nomi := &nonOrderlessMatchIter{}
	nomi.components = components
	nomi.lhs_components = lhs_components
	nomi.pm = CopyPD(pm)
	nomi.cl = cl

	// This function is now recursive because of the existence of BlankSequence.
	if nomi.cl.debugState {
		nomi.cl.Debugf("Entering NonOrderlessIsMatchQ(components: %s, lhs_components: %s, pm: %s)", ExArrayToString(nomi.components), ExArrayToString(nomi.lhs_components), nomi.pm)
	}
	if len(nomi.components) != 0 && len(nomi.lhs_components) == 0 {
		return nomi, false
	}

	nomi.progressI = 0
	return nomi, true
}

// I think for this to work, I must convert all MatchQ functions to iterators in
// the backend. Only the final MatchQ function should try the first match.
// Everything is an iterator that maintains its state. I think its just
// two other functions: NonOrderlessIsMatchQ and IsMatchQ. potentially need to convert consumers of these functions to use the iterator version.
func (this *nonOrderlessMatchIter) next() (bool, *PDManager, bool) {
	// A base case for the recursion
	if len(this.components) == 0 && len(this.lhs_components) == 0 {
		return true, this.pm, true
	}
	for i := 0; i < Max(len(this.components), len(this.lhs_components)); i++ {
		this.progressI = i
		if i >= len(this.lhs_components) {
			return false, this.pm, true
		}
		if i >= len(this.components) {
			this.cl.Debugf("Checking if IsMatchQ(INDEX_ERROR, %s). i=%d, Current context: %v\n", this.lhs_components[i], i, this.pm)
		} else {
			this.cl.Debugf("Checking if IsMatchQ(%s, %s). i=%d, Current context: %v\n", this.components[i], this.lhs_components[i], i, this.pm)
		}
		pat, isPat := HeadAssertion(this.lhs_components[i], "Pattern")
		bns, isBns := HeadAssertion(this.lhs_components[i], "BlankNullSequence")
		bs, isBs := HeadAssertion(this.lhs_components[i], "BlankSequence")
		if isPat {
			bns, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
			bs, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		}
		if isBns || isBs {
			this.cl.Debugf("Encountered BS or BNS!")
			remainingLhs := make([]Ex, len(this.lhs_components)-i-1)
			for k := i + 1; k < len(this.lhs_components); k++ {
				remainingLhs[k-i-1] = this.lhs_components[k].DeepCopy()
			}
			startI := 0
			if isBns {
				startI = i - 1
			} else {
				startI = i
			}
			for j := startI; j < len(this.components); j++ {
				// This process involves a lot of extraneous copying. I should
				// test to see how much of these arrays need to be copied from
				// scratch on every iteration.
				seqToTry := make([]Ex, j-i+1)
				for k := i; k <= j; k++ {
					seqToTry[k-i] = this.components[k].DeepCopy()
				}
				seqMatches := false
				if isBns {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankNullSequenceToBlank(bns), this.cl)
				} else {
					seqMatches = ExArrayTestRepeatingMatch(seqToTry, BlankSequenceToBlank(bs), this.cl)
				}
				this.cl.Debugf("%v", seqMatches)
				remainingComps := make([]Ex, len(this.components)-j-1)
				for k := j + 1; k < len(this.components); k++ {
					remainingComps[k-j-1] = this.components[k].DeepCopy()
				}
				if this.cl.debugState {
					this.cl.Debugf("%d %s %s %s", j, ExArrayToString(seqToTry), ExArrayToString(remainingComps), ExArrayToString(remainingLhs))
				}
				matchq, newPDs := NonOrderlessIsMatchQ(remainingComps, remainingLhs, this.pm, this.cl)
				if seqMatches && matchq {
					this.pm.Update(newPDs)
					if isPat {
						sAsSymbol, sAsSymbolOk := pat.Parts[1].(*Symbol)
						if sAsSymbolOk {
							toTryParts := []Ex{&Symbol{"Sequence"}}
							toTryParts = append(toTryParts, seqToTry...)
							target := NewExpression(toTryParts)
							_, ispd := this.pm.patternDefined[sAsSymbol.Name]
							if !ispd {
								this.pm.patternDefined[sAsSymbol.Name] = target
							}
							if !IsSameQ(this.pm.patternDefined[sAsSymbol.Name], target, this.cl) {
								return false, this.pm, true
							}
						}
					}
					return true, this.pm, true
				}
			}
			return false, this.pm, true
		}
		if i >= len(this.components) {
			return false, this.pm, true
		}
		ismatchq, toAdd := IsMatchQ(this.components[i].DeepCopy(), this.lhs_components[i], this.pm, this.cl)
		if ismatchq {
			this.cl.Debugf("Returned True!\n")
			this.pm.Update(toAdd)
		} else {
			this.cl.Debugf("NonOrderlessIsMatchQ failed. Context: %s", this.pm)
			return false, this.pm, true
		}
	}
	if this.progressI == len(this.lhs_components)-1 {
		return true, this.pm, true
	} else {
		return false, this.pm, true
	}
}

func (this *nonOrderlessMatchIter) reset() {}

func NonOrderlessIsMatchQ(components []Ex, lhs_components []Ex, pm *PDManager, cl *CASLogger) (bool, *PDManager) {
	nomi, ok := NewNonOrderlessMatchIter(components, lhs_components, pm, cl)
	if !ok {
		return false, pm
	}
	// Return the first match.
	matchq, newPd, _ := nomi.next()
	return matchq, newPd
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
