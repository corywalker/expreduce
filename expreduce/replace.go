package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// This function assumes e and lhs have the same head and that the head is Flat.
func flatReplace(
	e expreduceapi.ExpressionInterface,
	lhs expreduceapi.ExpressionInterface,
	rhs expreduceapi.Ex,
	orderless bool,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	looseLHS := atoms.NewExpression([]expreduceapi.Ex{})
	looseLHS.AppendEx(lhs.GetParts()[0])
	if !orderless {
		looseLHS.AppendEx(atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Pattern"),
			atoms.NewSymbol("System`Expreduce`start"),
			atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`BlankNullSequence")},
			),
		}))
	}
	looseLHS.AppendExArray(lhs.GetParts()[1:])
	looseLHS.AppendEx(atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`Pattern"),
		atoms.NewSymbol("System`Expreduce`end"),
		atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`BlankNullSequence")},
		),
	}))
	pm := matcher.EmptyPD()
	matchq, newPd := matcher.IsMatchQ(e, looseLHS, pm, es)
	if matchq {
		var tmpEx expreduceapi.Ex
		if orderless {
			tmpEx = matcher.ReplacePD(atoms.NewExpression([]expreduceapi.Ex{
				e.GetParts()[0],
				rhs,
				atoms.NewSymbol("System`Expreduce`end"),
			}),

				es, newPd)
		} else {
			tmpEx = matcher.ReplacePD(atoms.NewExpression([]expreduceapi.Ex{
				e.GetParts()[0],
				atoms.NewSymbol("System`Expreduce`start"),
				rhs,
				atoms.NewSymbol("System`Expreduce`end"),
			}),

				es, newPd)
		}
		return tmpEx
	}
	return e
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func replaceAll(
	this expreduceapi.Ex,
	r expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
	pm *matcher.PDManager,
	stopAtHead string,
) expreduceapi.Ex {
	asExpression, isExpression := this.(expreduceapi.ExpressionInterface)

	if isExpression {
		_, isRestrictedHead := atoms.HeadAssertion(this, stopAtHead)
		if isRestrictedHead {
			return this
		}
		// Continue recursion
		es.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
		return exprReplaceAll(asExpression, r, stopAtHead, es)
	}
	if res, matches := matcher.IsMatchQ(this, r.GetParts()[1], pm, es); res {
		return matcher.ReplacePD(r.GetParts()[2], es, matches)
	}
	return this
}

func tryCondWithMatches(
	rhs expreduceapi.Ex,
	matches *matcher.PDManager,
	es expreduceapi.EvalStateInterface,
) (expreduceapi.Ex, bool) {
	asCond, isCond := atoms.HeadAssertion(rhs, "System`Condition")
	if !isCond {
		if asWith, isWith := atoms.HeadAssertion(rhs, "System`With"); isWith {
			if len(asWith.GetParts()) == 3 {
				if _, hasCond := atoms.HeadAssertion(asWith.GetParts()[2], "System`Condition"); hasCond {
					appliedWith, ok := applyWithFn(asWith, es)
					if ok {
						asCond, isCond = atoms.HeadAssertion(
							appliedWith,
							"System`Condition",
						)
					}
				}
			}
		}
		if asMod, isMod := atoms.HeadAssertion(rhs, "System`Module"); isMod {
			if len(asMod.GetParts()) == 3 {
				if _, hasCond := atoms.HeadAssertion(asMod.GetParts()[2], "System`Condition"); hasCond {
					appliedMod, ok := applyModuleFn(asMod, es)
					if ok {
						asCond, isCond = atoms.HeadAssertion(
							appliedMod,
							"System`Condition",
						)
					}
				}
			}
		}
	}
	if isCond {
		condRes := es.Eval(asCond.GetParts()[2])
		condResSymbol, condResIsSymbol := condRes.(*atoms.Symbol)
		if condResIsSymbol {
			if condResSymbol.Name == "System`True" {
				return tryCondWithMatches(asCond.GetParts()[1], matches, es)
			}
		}
		return nil, false
	}
	return rhs, true
}

func replace(
	this expreduceapi.Ex,
	r expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) (expreduceapi.Ex, bool) {
	mi, cont := matcher.NewMatchIter(
		this,
		r.GetParts()[1],
		matcher.EmptyPD(),
		es,
	)
	for cont {
		res, matches, done := mi.Next()
		cont = !done
		if res {
			replacedRHS := matcher.ReplacePD(r.GetParts()[2], es, matches)
			toReturn, ok := tryCondWithMatches(replacedRHS, matches, es)
			if ok {
				return toReturn, true
			}
		}
	}
	return this, false
}
