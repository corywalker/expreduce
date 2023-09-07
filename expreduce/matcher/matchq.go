package matcher

import (
	"flag"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

var freezeStateDuringPreMatch = flag.Bool(
	"freezeStateDuringPreMatch",
	false,
	"Freeze the EvalState when doing a prematch pattern build. It is very "+
		"rare that this has any effect. We turn this feature off for better "+
		"thread safety.",
)

const maxUint = ^uint(0)
const maxInt = int(maxUint >> 1)

type MatchIter interface {
	// returns ismatch, pd, isdone
	Next() (bool, *PDManager, bool)
}

type dummyMatchIter struct {
	pm *PDManager
}

func (dmi *dummyMatchIter) Next() (bool, *PDManager, bool) {
	return true, dmi.pm, true
}

var realSym = atoms.NewSymbol("System`Real")
var intSym = atoms.NewSymbol("System`Integer")
var strSym = atoms.NewSymbol("System`String")
var symSym = atoms.NewSymbol("System`Symbol")
var ratSym = atoms.NewSymbol("System`Rational")
var complexSym = atoms.NewSymbol("System`Complex")

func NewMatchIter(
	a expreduceapi.Ex,
	b expreduceapi.Ex,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (MatchIter, bool) {
	patternHead := ""
	patExpr, patIsExpr := b.(expreduceapi.ExpressionInterface)
	if patIsExpr {
		sym, isSym := patExpr.GetParts()[0].(*atoms.Symbol)
		if isSym {
			patternHead = sym.Name
		}
	}
	if patternHead == "System`Except" {
		except := patExpr
		if len(except.GetParts()) == 2 {
			matchq, _ := IsMatchQ(a, except.GetParts()[1], pm, es)
			if !matchq {
				return &dummyMatchIter{pm}, true
			}
			return nil, false
		} else if len(except.GetParts()) == 3 {
			matchq, _ := IsMatchQ(a, except.GetParts()[1], pm, es)
			if !matchq {
				matchqb, newPm := IsMatchQ(a, except.GetParts()[2], pm, es)
				if matchqb {
					return &dummyMatchIter{newPm}, true
				}
			}
			return nil, false
		}
	} else if patternHead == "System`Alternatives" {
		alts := patExpr
		for _, alt := range alts.GetParts()[1:] {
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
		if len(patternTest.GetParts()) == 3 {
			matchq, newPD := IsMatchQ(a, patternTest.GetParts()[1], pm, es)
			if matchq {
				// Some Q functions are very simple and occur very often. For
				// some of these, skip the Eval() call and return the boolean
				// directly.
				testSym, testIsSym := patternTest.GetParts()[2].(*atoms.Symbol)
				if testIsSym {
					var qFunction (func(expreduceapi.Ex) bool)
					if testSym.Name == "System`NumberQ" {
						qFunction = atoms.NumberQ
					}
					if qFunction != nil {
						if qFunction(a) {
							return &dummyMatchIter{newPD}, true
						}
						return nil, false
					}
				}
				// I used to create a NewEvalState here, but I have evidence
				// that the same evalstate is used:
				// MatchQ[1, a_?((mytestval = 999; NumberQ[#]) &)] // Timing
				//tmpEs := NewEvalStateNoLog(true)
				res :=

					es.Eval((atoms.NewExpression([]expreduceapi.Ex{
						patternTest.GetParts()[2],
						a,
					})))

				resSymbol, resIsSymbol := res.(*atoms.Symbol)
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
		if len(condition.GetParts()) == 3 {
			mi, cont := NewMatchIter(a, condition.GetParts()[1], pm, es)
			for cont {
				matchq, newPD, done := mi.Next()
				cont = !done
				if matchq {
					//tmpEs := NewEvalStateNoLog(true)
					res := condition.GetParts()[2].DeepCopy()
					res = es.Eval(ReplacePD(res, es, newPD))
					resSymbol, resIsSymbol := res.(*atoms.Symbol)
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
		if len(optional.GetParts()) == 2 {
			matchq, newPD := IsMatchQ(a, optional.GetParts()[1], pm, es)
			if matchq {
				return &dummyMatchIter{newPD}, true
			}
		}
	} else if patternHead == "System`HoldPattern" {
		holdPattern := patExpr
		if len(holdPattern.GetParts()) == 2 {
			return NewMatchIter(a, holdPattern.GetParts()[1], pm, es)
		}
	}

	// Continue normally
	_, aIsFlt := a.(*atoms.Flt)
	_, aIsInteger := a.(*atoms.Integer)
	_, aIsString := a.(*atoms.String)
	_, aIsSymbol := a.(*atoms.Symbol)
	aRational, aIsRational := a.(*atoms.Rational)
	aComplex, aIsComplex := a.(*atoms.Complex)
	aExpression, aIsExpression := a.(expreduceapi.ExpressionInterface)
	bExpression, bIsExpression := b.(expreduceapi.ExpressionInterface)

	// Special case for the operator form of Verbatim
	forceOrdered := false
	verbatimOp, opExpr, isVerbatimOp := atoms.OperatorAssertion(
		b,
		"System`Verbatim",
	)
	if aIsExpression && isVerbatimOp {
		if len(opExpr.GetParts()) == 2 {
			if atoms.IsSameQ(aExpression.GetParts()[0], opExpr.GetParts()[1]) {
				b = atoms.NewExpression(
					append(
						[]expreduceapi.Ex{opExpr.GetParts()[1]},
						verbatimOp.GetParts()[1:]...),
				)
				bExpression, bIsExpression = b.(expreduceapi.ExpressionInterface)
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
		headEx = aExpression.GetParts()[0]
	} else if aIsSymbol {
		headEx = symSym
	} else if aIsRational {
		headEx = ratSym
	} else if aIsComplex {
		headEx = complexSym
	}

	if isBlankTypeOnly(b) {
		ibtc, ibtcNewPDs := isBlankTypeCapturing(
			b,
			a,
			headEx,
			pm,
			es.GetLogger(),
		)
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
		bExpressionSym, bExpressionSymOk := bExpression.GetParts()[0].(*atoms.Symbol)
		if bExpressionSymOk {
			oneIdentity := bExpressionSym.Attrs(es.GetDefinedMap()).OneIdentity
			hasDefaultExpr := bExpressionSym.Default(es.GetDefinedMap()) != nil
			containsOptional := false
			for _, part := range bExpression.GetParts()[1:] {
				if _, isOpt := atoms.HeadAssertion(part, "System`Optional"); isOpt {
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
			aExpression = atoms.NewExpression(
				[]expreduceapi.Ex{bExpressionSym, a},
			)
		}
		if aIsExpression {
			aExpressionSym, aExpressionSymOk := aExpression.GetParts()[0].(*atoms.Symbol)
			if canAssumeHead && aExpressionSymOk {
				if aExpressionSym.Name != bExpressionSym.Name {
					assumingHead = true
					aIsExpression = true
					aExpression = atoms.NewExpression(
						[]expreduceapi.Ex{bExpressionSym, a},
					)
				}
			}
		}
	}

	if !assumingHead {
		if aIsFlt || aIsInteger || aIsString || aIsSymbol || aIsRational ||
			aIsComplex {
			if atoms.IsSameQ(a, b) {
				return &dummyMatchIter{nil}, true
			}
			return nil, false
		} else if !(aIsExpression && bIsExpression) {
			return nil, false
		}
	}

	attrs := expreduceapi.Attributes{}
	sequenceHead := "Sequence"
	startI := 0
	aExpressionSym, aExpressionSymOk := aExpression.GetParts()[0].(*atoms.Symbol)
	bExpressionSym, bExpressionSymOk := bExpression.GetParts()[0].(*atoms.Symbol)
	if aExpressionSymOk && bExpressionSymOk {
		if aExpressionSym.Name == bExpressionSym.Name {
			attrs = aExpressionSym.Attrs(es.GetDefinedMap())
			sequenceHead = aExpressionSym.Name
			startI = 1
		}
	}

	isOrderless := attrs.Orderless && !forceOrdered
	isFlat := attrs.Flat && !forceOrdered
	nomi, ok := newSequenceMatchIter(
		aExpression.GetParts()[startI:],
		bExpression.GetParts()[startI:],
		isOrderless,
		isFlat,
		sequenceHead,
		pm,
		es,
	)
	if !ok {
		return nil, false
	}
	return nomi, true
}

func isMatchQRational(
	a *atoms.Rational,
	b expreduceapi.ExpressionInterface,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (bool, *PDManager) {
	return IsMatchQ(
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Rational"),
			atoms.NewInteger(a.Num),
			atoms.NewInteger(a.Den),
		}),

		b, pm, es)
}

func isMatchQComplex(
	a *atoms.Complex,
	b expreduceapi.ExpressionInterface,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (bool, *PDManager) {
	return IsMatchQ(
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Complex"),
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
	components    []expreduceapi.Ex
	lhsComponents []parsedForm
	pm            *PDManager
	sequenceHead  string
	es            expreduceapi.EvalStateInterface
	stack         []assignedIterState
}

func newAssignedMatchIter(
	assn [][]int,
	smi *sequenceMatchIter,
) assignedMatchIter {
	ami := assignedMatchIter{}
	ami.assn = assn
	ami.components = smi.components
	ami.lhsComponents = smi.lhsComponents
	ami.pm = smi.pm
	ami.sequenceHead = smi.sequenceHead
	ami.es = smi.es
	ami.stack = []assignedIterState{
		{0, 0, copyPD(ami.pm)},
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
		lhs := ami.lhsComponents[p.formI]
		if p.assnI >= len(ami.assn[p.formI]) {
			// Reached end of form. Attempt to define the sequence and continue
			// on success.
			seq := make([]expreduceapi.Ex, len(ami.assn[p.formI]))
			for i, assignedComp := range ami.assn[p.formI] {
				seq[i] = ami.components[assignedComp]
			}
			patOk := defineSequence(lhs, seq, p.pm, ami.sequenceHead, ami.es)
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
			matchq, submatches, done := mi.Next()
			cont = !done
			if matchq {
				// TODO: Perhaps check if submatches are different before
				// adding?
				toAddReversed = append(toAddReversed, submatches)
			}
		}
		for i := len(toAddReversed) - 1; i >= 0; i-- {
			updatedPm := p.pm
			if toAddReversed[i] != nil && toAddReversed[i].len() > 0 {
				if len(toAddReversed) > 1 {
					updatedPm = copyPD(p.pm)
				}
				updatedPm.update(toAddReversed[i])
			}
			ami.stack = append(ami.stack, assignedIterState{
				p.formI, p.assnI + 1, updatedPm,
			})
		}
	}
	return false
}

type sequenceMatchIter struct {
	components    []expreduceapi.Ex
	lhsComponents []parsedForm
	pm            *PDManager
	sequenceHead  string
	es            expreduceapi.EvalStateInterface
	ai            assnIter
	iteratingAmi  bool
	ami           assignedMatchIter
}

func newSequenceMatchIter(
	components []expreduceapi.Ex,
	lhsComponents []expreduceapi.Ex,
	isOrderless bool,
	isFlat bool,
	sequenceHead string,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (MatchIter, bool) {
	headDefault := (atoms.NewSymbol(sequenceHead)).Default(es.GetDefinedMap())
	fpComponents := make([]parsedForm, len(lhsComponents))
	for i, comp := range lhsComponents {
		fpComponents[i] = parseForm(
			comp,
			isFlat,
			sequenceHead,
			headDefault,
			es.GetLogger(),
		)
	}
	return newSequenceMatchIterPreparsed(
		components,
		fpComponents,
		isOrderless,
		sequenceHead,
		pm,
		es,
	)
}

func newSequenceMatchIterPreparsed(
	components []expreduceapi.Ex,
	lhsComponents []parsedForm,
	isOrderless bool,
	sequenceHead string,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (MatchIter, bool) {
	nomi := &sequenceMatchIter{}
	nomi.components = components
	nomi.lhsComponents = lhsComponents
	nomi.pm = pm
	nomi.sequenceHead = sequenceHead
	nomi.es = es

	origFrozen := es.IsFrozen()
	if *freezeStateDuringPreMatch {
		es.SetFrozen(true)
	}
	formMatches := make([][]bool, len(lhsComponents))
	for i, mustContain := range lhsComponents {
		// Right now I have this strange definition of "form". It's basically where I convert blank sequences to blanks at the bottom level. What if I did this at all levels and perhaps did something with patterns?
		// TODO: prevent the checks here from modifying state so I can use the "rm" function.
		formMatches[i] = make([]bool, len(components))
		numMatches := 0
		for j, part := range components {
			matchq, _ := IsMatchQ(part, mustContain.form, EmptyPD(), es)
			if matchq {
				numMatches++
			}
			formMatches[i][j] = matchq
		}
		if numMatches < mustContain.startI {
			if *freezeStateDuringPreMatch {
				es.SetFrozen(origFrozen)
			}
			return nomi, false
		}
	}
	if *freezeStateDuringPreMatch {
		es.SetFrozen(origFrozen)
	}

	nomi.ai = newAssnIter(
		len(components),
		lhsComponents,
		formMatches,
		isOrderless,
	)

	return nomi, true
}

func (smi *sequenceMatchIter) Next() (bool, *PDManager, bool) {
	for {
		if smi.iteratingAmi && smi.ami.next() {
			return true, smi.ami.pm, false
		}
		smi.iteratingAmi = false
		if !smi.ai.next() {
			break
		}
		smi.ami = newAssignedMatchIter(smi.ai.assns, smi)
		smi.iteratingAmi = true
	}
	return false, smi.pm, true
}

// HELPER FUNCTIONS

func getMatchQ(mi MatchIter, cont bool, pm *PDManager) (bool, *PDManager) {
	for cont {
		matchq, newPd, done := mi.Next()
		cont = !done
		// TODO: I could probably update my matchiters to only return if they
		// have a match or are done.
		if matchq {
			return true, newPd
		}
	}
	return false, pm
}

// IsMatchQ returns if an Ex `a` matches a pattern Ex `b`. If the expression
// matches the pattern and if the pattern has any named patterns, those matching
// values will be added to `pm`.
func IsMatchQ(
	a expreduceapi.Ex,
	b expreduceapi.Ex,
	pm *PDManager,
	es expreduceapi.EvalStateInterface,
) (bool, *PDManager) {
	mi, cont := NewMatchIter(a, b, pm, es)
	return getMatchQ(mi, cont, pm)
}
