package expreduce

import (
	"flag"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

var freezeStateDuringPreMatch = flag.Bool(
	"freezeStateDuringPreMatch",
	false,
	"Freeze the EvalState when doing a prematch pattern build. It is very "+
		"rare that this has any effect. We turn this feature off for better "+
		"thread safety.",
)

const MaxUint = ^uint(0)
const MaxInt = int(MaxUint >> 1)
const MaxUint64 = ^uint64(0)
const MaxInt64 = int64(MaxUint64 >> 1)

type matchIter interface {
	// returns ismatch, pd, isdone
	next() (bool, *PDManager, bool)
}

type dummyMatchIter struct {
	pm *PDManager
}

func (this *dummyMatchIter) next() (bool, *PDManager, bool) {
	return true, this.pm, true
}

var realSym = NewSymbol("System`Real")
var intSym = NewSymbol("System`Integer")
var strSym = NewSymbol("System`String")
var symSym = NewSymbol("System`Symbol")
var ratSym = NewSymbol("System`Rational")
var complexSym = NewSymbol("System`Complex")

func NewMatchIter(a expreduceapi.Ex, b expreduceapi.Ex, pm *PDManager, es *expreduceapi.EvalStateInterface) (matchIter, bool) {
	patternHead := ""
	patExpr, patIsExpr := b.(*expreduceapi.ExpressionInterface)
	if patIsExpr {
		sym, isSym := patExpr.Parts[0].(*Symbol)
		if isSym {
			patternHead = sym.Name
		}
	}
	if patternHead == "System`Except" {
		except := patExpr
		if len(except.Parts) == 2 {
			matchq, _ := IsMatchQ(a, except.Parts[1], pm, es)
			if !matchq {
				return &dummyMatchIter{pm}, true
			}
			return nil, false
		} else if len(except.Parts) == 3 {
			matchq, _ := IsMatchQ(a, except.Parts[1], pm, es)
			if !matchq {
				matchqb, newPm := IsMatchQ(a, except.Parts[2], pm, es)
				if matchqb {
					return &dummyMatchIter{newPm}, true
				}
			}
			return nil, false
		}
	} else if patternHead == "System`Alternatives" {
		alts := patExpr
		for _, alt := range alts.Parts[1:] {
			// I recently changed the third argument from EmptyPD() to pm
			// because MatchQ[{a, b}, {a_, k | a_}] was returning True, causing
			// problems in some of the boolean patterns. Might need to make
			// similar changes to the other pattern clauses.
			matchq, newPD := IsMatchQ(a, alt, pm, es)
			if matchq {
				return &dummyMatchIter{newPD}, true
			}
		}
		return nil, false
	} else if patternHead == "System`PatternTest" {
		patternTest := patExpr
		if len(patternTest.Parts) == 3 {
			matchq, newPD := IsMatchQ(a, patternTest.Parts[1], pm, es)
			if matchq {
				// Some Q functions are very simple and occur very often. For
				// some of these, skip the Eval() call and return the boolean
				// directly.
				testSym, testIsSym := patternTest.Parts[2].(*Symbol)
				if testIsSym {
					var qFunction singleParamQType
					if testSym.Name == "System`NumberQ" {
						qFunction = numberQ
					}
					if qFunction != nil {
						if qFunction(a) {
							return &dummyMatchIter{newPD}, true
						} else {
							return nil, false
						}
					}
				}
				// I used to create a NewEvalState here, but I have evidence
				// that the same evalstate is used:
				// MatchQ[1, a_?((mytestval = 999; NumberQ[#]) &)] // Timing
				//tmpEs := NewEvalStateNoLog(true)
				res := (NewExpression([]expreduceapi.Ex{
					patternTest.Parts[2],
					a,
				})).Eval(es)
				resSymbol, resIsSymbol := res.(*Symbol)
				if resIsSymbol {
					if resSymbol.Name == "System`True" {
						return &dummyMatchIter{newPD}, true
					}
				}
			}
			return nil, false
		}
	} else if patternHead == "System`Condition" {
		condition := patExpr
		if len(condition.Parts) == 3 {
			mi, cont := NewMatchIter(a, condition.Parts[1], pm, es)
			for cont {
				matchq, newPD, done := mi.next()
				cont = !done
				if matchq {
					//tmpEs := NewEvalStateNoLog(true)
					res := condition.Parts[2].DeepCopy()
					res = ReplacePD(res, es, newPD).Eval(es)
					resSymbol, resIsSymbol := res.(*Symbol)
					if resIsSymbol {
						if resSymbol.Name == "System`True" {
							return &dummyMatchIter{newPD}, true
						}
					}
				}
			}
		}
	} else if patternHead == "System`Optional" {
		optional := patExpr
		if len(optional.Parts) == 2 {
			matchq, newPD := IsMatchQ(a, optional.Parts[1], pm, es)
			if matchq {
				return &dummyMatchIter{newPD}, true
			}
		}
	} else if patternHead == "System`HoldPattern" {
		holdPattern := patExpr
		if len(holdPattern.Parts) == 2 {
			return NewMatchIter(a, holdPattern.Parts[1], pm, es)
		}
	}

	// Continue normally
	_, aIsFlt := a.(*Flt)
	_, aIsInteger := a.(*Integer)
	_, aIsString := a.(*String)
	_, aIsSymbol := a.(*Symbol)
	aRational, aIsRational := a.(*Rational)
	aComplex, aIsComplex := a.(*Complex)
	aExpression, aIsExpression := a.(*expreduceapi.ExpressionInterface)
	bExpression, bIsExpression := b.(*expreduceapi.ExpressionInterface)

	// Special case for the operator form of Verbatim
	forceOrdered := false
	verbatimOp, opExpr, isVerbatimOp := OperatorAssertion(b, "System`Verbatim")
	if aIsExpression && isVerbatimOp {
		if len(opExpr.Parts) == 2 {
			if IsSameQ(aExpression.Parts[0], opExpr.Parts[1], &es.CASLogger) {
				b = NewExpression(append([]expreduceapi.Ex{opExpr.Parts[1]}, verbatimOp.Parts[1:]...))
				bExpression, bIsExpression = b.(*expreduceapi.ExpressionInterface)
				forceOrdered = true
			}
		}
	}

	// This initial value is just a randomly chosen placeholder
	var headEx expreduceapi.Ex
	if aIsFlt {
		headEx = realSym
	} else if aIsInteger {
		headEx = intSym
	} else if aIsString {
		headEx = strSym
	} else if aIsExpression {
		headEx = aExpression.Parts[0]
	} else if aIsSymbol {
		headEx = symSym
	} else if aIsRational {
		headEx = ratSym
	} else if aIsComplex {
		headEx = complexSym
	}

	if IsBlankTypeOnly(b) {
		ibtc, ibtcNewPDs := IsBlankTypeCapturing(b, a, headEx, pm, &es.CASLogger)
		if ibtc {
			return &dummyMatchIter{ibtcNewPDs}, true
		}
		return nil, false
	}

	// Handle special case for matching Rational[a_Integer, b_Integer]
	if aIsRational && bIsExpression {
		matchq, newPm := isMatchQRational(aRational, bExpression, pm, es)
		if matchq {
			return &dummyMatchIter{newPm}, true
		}
		return nil, false
	}

	// Handle special case for matching Complex[a, b]
	if aIsComplex && bIsExpression {
		matchq, newPm := isMatchQComplex(aComplex, bExpression, pm, es)
		if matchq {
			return &dummyMatchIter{newPm}, true
		}
		return nil, false
	}

	canAssumeHead := false
	assumingHead := false
	if bIsExpression {
		bExpressionSym, bExpressionSymOk := bExpression.Parts[0].(*Symbol)
		if bExpressionSymOk {
			oneIdentity := bExpressionSym.Attrs(&es.defined).OneIdentity
			hasDefaultExpr := bExpressionSym.Default(&es.defined) != nil
			containsOptional := false
			for _, part := range bExpression.Parts[1:] {
				if _, isOpt := HeadAssertion(part, "System`Optional"); isOpt {
					containsOptional = true
					break
				}
			}
			if oneIdentity && hasDefaultExpr && containsOptional {
				canAssumeHead = true
			}
		}

		// Handle special case where MatchQ[a,a+c_.] is True
		if canAssumeHead && !aIsExpression {
			// Normally this would always fail, but if the conditions are right,
			// let's configure the variables such that we at least try for a
			// sequence match.
			assumingHead = true
			aIsExpression = true
			aExpression = NewExpression([]expreduceapi.Ex{bExpressionSym, a})
		}
		if aIsExpression {
			aExpressionSym, aExpressionSymOk := aExpression.Parts[0].(*Symbol)
			if canAssumeHead && aExpressionSymOk {
				if aExpressionSym.Name != bExpressionSym.Name {
					assumingHead = true
					aIsExpression = true
					aExpression = NewExpression([]expreduceapi.Ex{bExpressionSym, a})
				}
			}
		}
	}

	if !assumingHead {
		if aIsFlt || aIsInteger || aIsString || aIsSymbol || aIsRational || aIsComplex {
			if IsSameQ(a, b, &es.CASLogger) {
				return &dummyMatchIter{nil}, true
			}
			return nil, false
		} else if !(aIsExpression && bIsExpression) {
			return nil, false
		}
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

	isOrderless := attrs.Orderless && !forceOrdered
	isFlat := attrs.Flat && !forceOrdered
	nomi, ok := NewSequenceMatchIter(aExpression.Parts[startI:], bExpression.Parts[startI:], isOrderless, isFlat, sequenceHead, pm, es)
	if !ok {
		return nil, false
	}
	return nomi, true
}

func isMatchQRational(a *Rational, b *expreduceapi.ExpressionInterface, pm *PDManager, es *expreduceapi.EvalStateInterface) (bool, *PDManager) {
	return IsMatchQ(
		NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Rational"),
			NewInteger(a.Num),
			NewInteger(a.Den),
		}),

		b, pm, es)
}

func isMatchQComplex(a *Complex, b *expreduceapi.ExpressionInterface, pm *PDManager, es *expreduceapi.EvalStateInterface) (bool, *PDManager) {
	return IsMatchQ(
		NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Complex"),
			a.Re,
			a.Im,
		}),

		b, pm, es)
}

type assignedIterState struct {
	formI int
	assnI int
	pm    *PDManager
}

type assignedMatchIter struct {
	assn [][]int

	// Inherited from sequenceMatchIter
	components     []expreduceapi.Ex
	lhs_components []parsedForm
	pm             *PDManager
	sequenceHead   string
	es             *expreduceapi.EvalStateInterface
	stack          []assignedIterState
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
		{0, 0, CopyPD(ami.pm)},
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
			seq := make([]expreduceapi.Ex, len(ami.assn[p.formI]))
			for i, assignedComp := range ami.assn[p.formI] {
				seq[i] = ami.components[assignedComp]
			}
			patOk := DefineSequence(lhs, seq, p.pm, ami.sequenceHead, ami.es)
			if patOk {
				ami.stack = append(ami.stack, assignedIterState{
					p.formI + 1, 0, p.pm,
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
		for i := len(toAddReversed) - 1; i >= 0; i-- {
			updatedPm := p.pm
			if toAddReversed[i] != nil && toAddReversed[i].Len() > 0 {
				if len(toAddReversed) > 1 {
					updatedPm = CopyPD(p.pm)
				}
				updatedPm.Update(toAddReversed[i])
			}
			ami.stack = append(ami.stack, assignedIterState{
				p.formI, p.assnI + 1, updatedPm,
			})
		}
	}
	return false
}

type sequenceMatchIter struct {
	components     []expreduceapi.Ex
	lhs_components []parsedForm
	pm             *PDManager
	sequenceHead   string
	es             *expreduceapi.EvalStateInterface
	ai             assnIter
	iteratingAmi   bool
	ami            assignedMatchIter
}

func NewSequenceMatchIter(components []expreduceapi.Ex, lhs_components []expreduceapi.Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *expreduceapi.EvalStateInterface) (matchIter, bool) {
	headDefault := (NewSymbol(sequenceHead)).Default(&es.defined)
	fp_components := make([]parsedForm, len(lhs_components))
	for i, comp := range lhs_components {
		fp_components[i] = ParseForm(comp, isFlat, sequenceHead, headDefault, &es.CASLogger)
	}
	return NewSequenceMatchIterPreparsed(components, fp_components, isOrderless, sequenceHead, pm, es)
}

func NewSequenceMatchIterPreparsed(components []expreduceapi.Ex, lhs_components []parsedForm, isOrderless bool, sequenceHead string, pm *PDManager, es *expreduceapi.EvalStateInterface) (matchIter, bool) {
	nomi := &sequenceMatchIter{}
	nomi.components = components
	nomi.lhs_components = lhs_components
	nomi.pm = pm
	nomi.sequenceHead = sequenceHead
	nomi.es = es

	origFrozen := es.IsFrozen()
	if *freezeStateDuringPreMatch {
		es.SetFrozen(true)
	}
	formMatches := make([][]bool, len(lhs_components))
	for i, mustContain := range lhs_components {
		// Right now I have this strange definition of "form". It's basically where I convert blank sequences to blanks at the bottom level. What if I did this at all levels and perhaps did something with patterns?
		// TODO: prevent the checks here from modifying state so I can use the "rm" function.
		formMatches[i] = make([]bool, len(components))
		num_matches := 0
		for j, part := range components {
			matchq, _ := IsMatchQ(part, mustContain.form, EmptyPD(), es)
			if matchq {
				num_matches++
			}
			formMatches[i][j] = matchq
		}
		if num_matches < mustContain.startI {
			if *freezeStateDuringPreMatch {
				es.SetFrozen(origFrozen)
			}
			return nomi, false
		}
	}
	if *freezeStateDuringPreMatch {
		es.SetFrozen(origFrozen)
	}

	nomi.ai = NewAssnIter(len(components), lhs_components, formMatches, isOrderless)

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

func ComponentsIsMatchQ(components []expreduceapi.Ex, lhs_components []expreduceapi.Ex, isOrderless bool, isFlat bool, sequenceHead string, pm *PDManager, es *expreduceapi.EvalStateInterface) (bool, *PDManager) {
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
func IsMatchQ(a expreduceapi.Ex, b expreduceapi.Ex, pm *PDManager, es *expreduceapi.EvalStateInterface) (bool, *PDManager) {
	mi, cont := NewMatchIter(a, b, pm, es)
	return GetMatchQ(mi, cont, pm)
}
