package expreduce

const MaxUint = ^uint(0)
const MaxInt = int(MaxUint >> 1)

type matchIter interface {
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

	nomi, ok := NewSequenceMatchIter(aExpression.Parts[startI:], bExpression.Parts[startI:], attrs.Orderless, attrs.Flat, sequenceHead, pm, es)
	if !ok {
		return &dummyMatchIter{false, pm, true}, true
	}
	return nomi, true
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

type assignedIterState struct {
	formI int
	assnI int
	pm *PDManager
}

type assignedMatchIter struct {
	assn			[][]int

	// Inherited from sequenceMatchIter
	components		[]Ex
	lhs_components	[]parsedForm
	pm				*PDManager
	sequenceHead	string
	es				*EvalState
	stack			[]assignedIterState
}

func NewAssignedMatchIter(assn [][]int, smi *sequenceMatchIter) assignedMatchIter {
	ami := assignedMatchIter{}
	ami.assn = assn
	ami.components = smi.components
	ami.lhs_components = smi.lhs_components
	ami.pm = smi.pm
	ami.sequenceHead = smi.sequenceHead
	ami.es = smi.es
	ami.stack = []assignedIterState{
		assignedIterState{0, 0, CopyPD(ami.pm)},
	}
	return ami
}

func (ami *assignedMatchIter) next() bool {
	for len(ami.stack) > 0 {
		var p assignedIterState
		l := len(ami.stack)
		ami.stack, p = ami.stack[:l-1], ami.stack[l-1]

		if p.formI >= len(ami.assn) {
			// We found a sequence match!
			ami.pm = p.pm
			return true
		}
		lhs := ami.lhs_components[p.formI]
		if p.assnI >= len(ami.assn[p.formI]) {
			// Reached end of form. Attempt to define the sequence and continue
			// on success.
			seq := make([]Ex, len(ami.assn[p.formI]))
			for i, assignedComp := range ami.assn[p.formI] {
				seq[i] = ami.components[assignedComp]
			}
			patOk := DefineSequence(lhs.origForm, seq, lhs.isBlank, p.pm, lhs.isImpliedBs, ami.sequenceHead, ami.es)
			if patOk {
				ami.stack = append(ami.stack, assignedIterState{
					p.formI+1, 0, p.pm,
				})
			}
			continue
		}

		//matches, newPm := IsMatchQ(comp, lhs.form, p.pm, ami.es)
		//if matches {
		comp := ami.components[ami.assn[p.formI][p.assnI]]
		toAddReversed := []*PDManager{}
		mi, cont := NewMatchIter(comp, lhs.form, p.pm, ami.es)
		for cont {
			matchq, submatches, done := mi.next()
			cont = !done
			if matchq {
				// TODO: Perhaps check if submatches are different before
				// adding?
				toAddReversed = append(toAddReversed, submatches)
			}
		}
		for i := len(toAddReversed)-1; i >= 0; i-- {
			updatedPm := p.pm
			if toAddReversed[i].Len() > 0 {
				if len(toAddReversed) > 1 {
					updatedPm = CopyPD(p.pm)
				}
				updatedPm.Update(toAddReversed[i])
			}
			ami.stack = append(ami.stack, assignedIterState{
				p.formI, p.assnI+1, updatedPm,
			})
		}
	}
	return false
}

type sequenceMatchIter struct {
	components		[]Ex
	lhs_components	[]parsedForm
	pm				*PDManager
	sequenceHead	string
	es				*EvalState
	ai				assnIter
	iteratingAmi	bool
	ami				assignedMatchIter
}

func NewSequenceMatchIter(components []Ex, lhs_components []Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *EvalState) (matchIter, bool) {
	fp_components := make([]parsedForm, len(lhs_components))
	for i, comp := range lhs_components {
		fp_components[i] = ParseForm(comp, isFlat, sequenceHead, &es.CASLogger)
	}
	return NewSequenceMatchIterPreparsed(components, fp_components, isOrderless, sequenceHead, pm, es)
}

func NewSequenceMatchIterPreparsed(components []Ex, lhs_components []parsedForm, isOrderless bool, sequenceHead string, pm *PDManager, es *EvalState) (matchIter, bool) {
	nomi := &sequenceMatchIter{}
	nomi.components = components
	nomi.lhs_components = lhs_components
	nomi.pm = pm
	nomi.sequenceHead = sequenceHead
	nomi.es = es

	for _, mustContain := range lhs_components {
		if mustContain.startI > 0 && !MemberQ(components, mustContain.form, es) {
			return nomi, false
		}
	}

	nomi.ai = NewAssnIter(len(components), lhs_components, isOrderless)

	return nomi, true
}

func (this *sequenceMatchIter) next() (bool, *PDManager, bool) {
	for {
		if this.iteratingAmi && this.ami.next() {
			return true, this.ami.pm, false
		}
		this.iteratingAmi = false
		if !this.ai.next() {
			break
		}
		this.ami = NewAssignedMatchIter(this.ai.assns, this)
		this.iteratingAmi = true
	}
	return false, this.pm, true
}

// HELPER FUNCTIONS

func ComponentsIsMatchQ(components []Ex, lhs_components []Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *EvalState) (bool, *PDManager) {
	omi, cont := NewSequenceMatchIter(components, lhs_components, isOrderless, isFlat, sequenceHead, pm, es)
	return GetMatchQ(omi, cont, pm)
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

// TODO: do not export this
func IsMatchQ(a Ex, b Ex, pm *PDManager, es *EvalState) (bool, *PDManager) {
	mi, cont := NewMatchIter(a, b, pm, es)
	return GetMatchQ(mi, cont, pm)
}
