package expreduce

import "fmt"

const MaxUint = ^uint(0)
const MaxInt = int(MaxUint >> 1)

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

type multiMatchIter struct {
	matchIters	[]matchIter
	i			int
}

func (this *multiMatchIter) next() (bool, *PDManager, bool) {
	if this.i >= len(this.matchIters) {
		return false, EmptyPD(), true
	}
	matchq, newPd, done := this.matchIters[this.i].next()
	if done {
		this.i++
	}
	done = this.i >= len(this.matchIters)
	return matchq, newPd, done
}

func (this *multiMatchIter) reset() {}

func NewMatchIter(a Ex, b Ex, pm *PDManager, es *EvalState) (matchIter, bool) {
	// Special case for Except
	except, isExcept := HeadAssertion(b, "Except")
	if isExcept {
		if len(except.Parts) == 2 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), es)
			return &dummyMatchIter{!matchq, pm, true}, true
		} else if len(except.Parts) == 3 {
			matchq, _ := IsMatchQ(a, except.Parts[1], EmptyPD(), es)
			if !matchq {
				matchqb, newPm := IsMatchQ(a, except.Parts[2], pm, es)
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
			matchq, newPD := IsMatchQ(a, alt, pm, es)
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
			matchq, newPD := IsMatchQ(a, patternTest.Parts[1], EmptyPD(), es)
			if matchq {
				// I used to create a NewEvalState here, but I have evidence
				// that the same evalstate is used:
				// MatchQ[1, a_?((mytestval = 999; NumberQ[#]) &)] // Timing
				//tmpEs := NewEvalStateNoLog(true)
				res := (NewExpression([]Ex{
					patternTest.Parts[2],
					a,
				})).Eval(es)
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
			mi, cont := NewMatchIter(a, condition.Parts[1], EmptyPD(), es)
			for cont {
				matchq, newPD, done := mi.next()
				cont = !done
				if matchq {
					//tmpEs := NewEvalStateNoLog(true)
					res := condition.Parts[2].DeepCopy()
					res = ReplacePD(res, es, newPD).Eval(es)
					resSymbol, resIsSymbol := res.(*Symbol)
					if resIsSymbol {
						if resSymbol.Name == "True" {
							return &dummyMatchIter{true, newPD, true}, true
						}
					}
				}
			}
		}
	}

	// Continue normally
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
		ibtc, ibtcNewPDs := IsBlankTypeCapturing(b, a, headStr, pm, &es.CASLogger)
		if ibtc {
			return &dummyMatchIter{true, ibtcNewPDs, true}, true
		}
		return &dummyMatchIter{false, EmptyPD(), true}, true
	}

	// Handle special case for matching Rational[a_Integer, b_Integer]
	if aIsRational && bIsExpression {
		matchq, newPm := isMatchQRational(aRational, bExpression, pm, es)
		return &dummyMatchIter{matchq, newPm, true}, true
	} else if aIsExpression && bIsRational {
		matchq, newPm := isMatchQRational(bRational, aExpression, pm, es)
		return &dummyMatchIter{matchq, newPm, true}, true
	}

	if aIsFlt || aIsInteger || aIsString || aIsSymbol || aIsRational {
		return &dummyMatchIter{IsSameQ(a, b, &es.CASLogger), EmptyPD(), true}, true
	} else if !(aIsExpression && bIsExpression) {
		return &dummyMatchIter{false, EmptyPD(), true}, true
	}

	attrs := Attributes{}
	sequenceHead := "Sequence"
	startI := 0
	aExpressionSym, aExpressionSymOk := aExpression.Parts[0].(*Symbol)
	bExpressionSym, bExpressionSymOk := bExpression.Parts[0].(*Symbol)
	if aExpressionSymOk && bExpressionSymOk {
		if aExpressionSym.Name == bExpressionSym.Name {
			attrs = aExpressionSym.Attrs(&es.defined)
			sequenceHead = aExpressionSym.Name
			startI = 1
		}
	}

	nomi, ok := NewSequenceMatchIter(aExpression.Parts[startI:], bExpression.Parts[startI:], []Ex{}, attrs.Orderless, attrs.Flat, sequenceHead, pm, es)
	if !ok {
		return &dummyMatchIter{false, pm, true}, true
	}
	return nomi, true
}

// TODO: do not export this
func IsMatchQ(a Ex, b Ex, pm *PDManager, es *EvalState) (bool, *PDManager) {
	mi, cont := NewMatchIter(a, b, pm, es)
	return GetMatchQ(mi, cont, pm)
}

func isMatchQRational(a *Rational, b *Expression, pm *PDManager, es *EvalState) (bool, *PDManager) {
	return IsMatchQ(
		NewExpression([]Ex{
			&Symbol{"Rational"},
			&Integer{a.Num},
			&Integer{a.Den},
		}),

		b, pm, es)
}

func ParseRepeated(e *Expression) (Ex, int, int, bool) {
	min, max := -1, -1
	if len(e.Parts) < 2 {
		return nil, min, max, false
	}
	if len(e.Parts) >= 3 {
		list, isList := HeadAssertion(e.Parts[2], "List")
		if !isList {
			return nil, min, max, false
		}
		if len(list.Parts) != 2 {
			return nil, min, max, false
		}
		i, isInt := list.Parts[1].(*Integer)
		if !isInt {
			return nil, min, max, false
		}
		ival := i.Val.Int64()
		min = int(ival)
		max = min
	}
	return e.Parts[1], min, max, true
}

func GetMatchQ(mi matchIter, cont bool, pm *PDManager) (bool, *PDManager) {
	for cont {
		matchq, newPd, done := mi.next()
		cont = !done
		// TODO: I could probably update my matchiters to only return if they
		// have a match or are done.
		if matchq {
			return true, newPd
		}
	}
	return false, pm
}

type sequenceMatchIter struct {
	components		[]Ex
	lhs_components	[]parsedForm
	match_components	[]Ex
	pm				*PDManager
	remainingMatchIter matchIter
	isFlat			bool
	isOrderless		bool
	sequenceHead	string
	es				*EvalState
	ai				assnIter
}

func NewSequenceMatchIter(components []Ex, lhs_components []Ex, match_components []Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *EvalState) (matchIter, bool) {
	fp_components := make([]parsedForm, len(lhs_components))
	for i, comp := range lhs_components {
		fp_components[i] = ParseForm(comp, isFlat, sequenceHead, &es.CASLogger)
	}
	return NewSequenceMatchIterPreparsed(components, fp_components, match_components, isOrderless, isFlat, sequenceHead, pm, es)
}

func NewSequenceMatchIterPreparsed(components []Ex, lhs_components []parsedForm, match_components []Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *EvalState) (matchIter, bool) {
	nomi := &sequenceMatchIter{}
	nomi.components = components
	nomi.lhs_components = lhs_components
	nomi.match_components = match_components
	nomi.pm = pm
	nomi.isFlat = isFlat
	nomi.isOrderless = isOrderless
	nomi.sequenceHead = sequenceHead
	nomi.es = es

	for _, mustContain := range lhs_components {
		if mustContain.startI > 0 && !MemberQ(components, mustContain.form, es) {
			return nomi, false
		}
	}

	nomi.ai = NewAssnIter(len(components), lhs_components, nomi.isOrderless)

	// This function is now recursive because of the existence of BlankSequence.
	return nomi, true
}

func DefineSequence(lhs_component Ex, sequence []Ex, isBlank bool, pm *PDManager, isImpliedBs bool, sequenceHead string, es *EvalState) bool {
	pat, isPat := HeadAssertion(lhs_component, "Pattern")
	if !isPat {
		return true
	}
	sAsSymbol, sAsSymbolOk := pat.Parts[1].(*Symbol)
	var attemptDefine Ex = nil
	if sAsSymbolOk {
		sequenceHeadSym := &Symbol{sequenceHead}
		oneIdent := sequenceHeadSym.Attrs(&es.defined).OneIdentity
		if len(sequence) == 1 && (isBlank || oneIdent) {
			if len(sequence) != 1 {
				fmt.Println("Invalid blank components length!!")
			}
			attemptDefine = sequence[0]
		} else if isImpliedBs {
			attemptDefine = NewExpression(append([]Ex{sequenceHeadSym}, sequence...))
		} else {
			head := &Symbol{"Sequence"}
			attemptDefine = NewExpression(append([]Ex{head}, sequence...))
		}

		if attemptDefine != nil {
			defined, ispd := pm.patternDefined[sAsSymbol.Name]
			if ispd && !IsSameQ(defined, attemptDefine, &es.CASLogger) {
				es.Debugf("patterns do not match! continuing.")
				return false
			}
			pm.patternDefined[sAsSymbol.Name] = attemptDefine
		}
	}
	return true
}

type parsedForm struct {
	startI		int
	endI		int
	form		Ex
	origForm	Ex
	isBlank		bool
	isImpliedBs	bool
	formHasPattern	bool
}

func ParseForm(lhs_component Ex, isFlat bool, sequenceHead string, cl *CASLogger) (res parsedForm) {
	// Calculate the min and max elements this component can match.
	pat, isPat := HeadAssertion(lhs_component, "Pattern")
	bns, isBns := HeadAssertion(lhs_component, "BlankNullSequence")
	bs, isBs := HeadAssertion(lhs_component, "BlankSequence")
	blank, isBlank := HeadAssertion(lhs_component, "Blank")
	repeated, isRepeated := HeadAssertion(lhs_component, "Repeated")
	if isPat {
		bns, isBns = HeadAssertion(pat.Parts[2], "BlankNullSequence")
		bs, isBs = HeadAssertion(pat.Parts[2], "BlankSequence")
		blank, isBlank = HeadAssertion(pat.Parts[2], "Blank")
		repeated, isRepeated = HeadAssertion(pat.Parts[2], "Repeated")
	}
	isImpliedBs := isBlank && isFlat
	// Ensure isBlank is exclusive from isImpliedBs
	isBlank = isBlank && !isImpliedBs

	form := lhs_component
	startI := 1 // also includes implied blanksequence
	endI := 1

	if isBns {
		form = BlankNullSequenceToBlank(bns)
		startI = 0
		endI = MaxInt
	} else if isImpliedBs {
		form = blank
		endI = MaxInt
		if len(blank.Parts) >= 2 {
			sym, isSym := blank.Parts[1].(*Symbol)
			if isSym {
				// If we have a pattern like k__Plus
				if sym.Name == sequenceHead {
					form = NewExpression([]Ex{&Symbol{"Blank"}})
					startI = 2
				} else {
					endI = 1
				}
			}
		}
	} else if isBlank {
		form = blank
	} else if isRepeated {
		repPat, repMin, repMax, repOk := ParseRepeated(repeated)
		if (repOk) {
			if repMin != -1 {
				startI = repMin
			}
			if repMax != -1 {
				endI = repMax
			} else {
				// an undefined end can match to the end of the sequence.
				endI = MaxInt
			}
			form = repPat
		}
	} else if isBs {
		form = BlankSequenceToBlank(bs)
		endI = MaxInt
	}
	cl.Debugf("Determined sequence startI = %v, endI = %v", startI, endI)

	res.startI = startI
	res.endI = endI
	res.form = form
	res.origForm = lhs_component
	_, res.formHasPattern = HeadAssertion(form, "Pattern")
	res.isImpliedBs = isImpliedBs
	res.isBlank = isBlank
	return res
}

func (this *sequenceMatchIter) next() (bool, *PDManager, bool) {
	if !this.ai.next() {
		return false, this.pm, true
	}
	updatedPm := CopyPD(this.pm)
	for formI, formAssn := range this.ai.assns {
		lhs := this.lhs_components[formI]
		seq := make([]Ex, len(formAssn))
		for assnI, assn := range formAssn {
			comp := this.components[assn]
			matches, newPm := IsMatchQ(comp, lhs.form, updatedPm, this.es)
			if !matches {
				return false, this.pm, false
			}
			updatedPm.Update(newPm)
			seq[assnI] = comp
		}
		patOk := DefineSequence(lhs.origForm, seq, lhs.isBlank, updatedPm, lhs.isImpliedBs, this.sequenceHead, this.es)
		if !patOk {
			return false, this.pm, false
		}
	}

	return true, updatedPm, false
}

func (this *sequenceMatchIter) reset() {}

func ComponentsIsMatchQ(components []Ex, lhs_components []Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *EvalState) (bool, *PDManager) {
	omi, cont := NewSequenceMatchIter(components, lhs_components, []Ex{}, isOrderless, isFlat, sequenceHead, pm, es)
	return GetMatchQ(omi, cont, pm)
}
