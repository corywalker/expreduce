package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

// This function assumes e and lhs have the same head and that the head is Flat.
func FlatReplace(e expreduceapi.ExpressionInterface, lhs expreduceapi.ExpressionInterface, rhs expreduceapi.Ex, orderless bool, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	looseLhs := NewExpression([]expreduceapi.Ex{})
	looseLhs.AppendEx(lhs.GetParts()[0])
	if !orderless {
		looseLhs.AppendEx(NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Pattern"),
			NewSymbol("System`Expreduce`start"),
			NewExpression([]expreduceapi.Ex{NewSymbol("System`BlankNullSequence")}),
		}))
	}
	looseLhs.AppendExArray(lhs.GetParts()[1:])
	looseLhs.AppendEx(NewExpression([]expreduceapi.Ex{
		NewSymbol("System`Pattern"),
		NewSymbol("System`Expreduce`end"),
		NewExpression([]expreduceapi.Ex{NewSymbol("System`BlankNullSequence")}),
	}))
	pm := EmptyPD()
	matchq, newPd := IsMatchQ(e, looseLhs, pm, es)
	if matchq {
		var tmpEx expreduceapi.Ex
		if orderless {
			tmpEx = ReplacePD(NewExpression([]expreduceapi.Ex{
				e.GetParts()[0],
				rhs,
				NewSymbol("System`Expreduce`end"),
			}), es, newPd)
		} else {
			tmpEx = ReplacePD(NewExpression([]expreduceapi.Ex{
				e.GetParts()[0],
				NewSymbol("System`Expreduce`start"),
				rhs,
				NewSymbol("System`Expreduce`end"),
			}), es, newPd)
		}
		return tmpEx
	}
	return e
}

func ReplacePDInternal(e expreduceapi.Ex, pm *PDManager) (expreduceapi.Ex, bool) {
	asSym, isSym := e.(*Symbol)
	if isSym {
		for k, def := range pm.patternDefined {
			if k == asSym.Name {
				// Shouldn't need the copy
				return def, true
			}
		}
	}
	thisDirty := false
	asExpr, isExpr := e.(expreduceapi.ExpressionInterface)
	if isExpr {
		for i := range asExpr.GetParts() {
			possiblyNewExpr, dirty := ReplacePDInternal(asExpr.GetParts()[i], pm)
			if dirty {
				thisDirty = true
				// Mark the expression as dirty and needing eval.
				asExpr.ClearHashes()
			}
			asExpr.GetParts()[i] = possiblyNewExpr
		}
	}
	return e, thisDirty
}

func ReplacePD(this expreduceapi.Ex, es expreduceapi.EvalStateInterface, pm *PDManager) expreduceapi.Ex {
	if pm == nil {
		return this
	}
	containsAny := false
	for k := range pm.patternDefined {
		if ContainsSymbol(this, k) {
			containsAny = true
			break
		}
	}
	if !containsAny {
		return this
	}

	// Expressions are immutable. Any time we change an expression, we must
	// first copy it.
	res, _ := ReplacePDInternal(this.Copy(), pm)
	return res
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func ReplaceAll(this expreduceapi.Ex, r expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface, pm *PDManager,
	stopAtHead string) expreduceapi.Ex {
	asExpression, isExpression := this.(expreduceapi.ExpressionInterface)

	if isExpression {
		_, isRestrictedHead := HeadAssertion(this, stopAtHead)
		if isRestrictedHead {
			return this
		} else {
			// Continue recursion
			es.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
			return ExprReplaceAll(asExpression, r, stopAtHead, es)
		}
	}
	if res, matches := IsMatchQ(this, r.GetParts()[1], pm, es); res {
		return ReplacePD(r.GetParts()[2], es, matches)
	}
	return this
}

func tryCondWithMatches(rhs expreduceapi.Ex, matches *PDManager, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, bool) {
	asCond, isCond := HeadAssertion(rhs, "System`Condition")
	if !isCond {
		if asWith, isWith := HeadAssertion(rhs, "System`With"); isWith {
			if len(asWith.GetParts()) == 3 {
				if _, hasCond := HeadAssertion(asWith.GetParts()[2], "System`Condition"); hasCond {
					appliedWith, ok := applyWithFn(asWith, es)
					if ok {
						asCond, isCond = HeadAssertion(appliedWith, "System`Condition")
					}
				}
			}
		}
		if asMod, isMod := HeadAssertion(rhs, "System`Module"); isMod {
			if len(asMod.GetParts()) == 3 {
				if _, hasCond := HeadAssertion(asMod.GetParts()[2], "System`Condition"); hasCond {
					appliedMod, ok := applyModuleFn(asMod, es)
					if ok {
						asCond, isCond = HeadAssertion(appliedMod, "System`Condition")
					}
				}
			}
		}
	}
	if isCond {
		condRes := asCond.GetParts()[2].Eval(es)
		condResSymbol, condResIsSymbol := condRes.(*Symbol)
		if condResIsSymbol {
			if condResSymbol.Name == "System`True" {
				return tryCondWithMatches(asCond.GetParts()[1], matches, es)
			}
		}
		return nil, false
	}
	return rhs, true
}

func Replace(this expreduceapi.Ex, r expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, bool) {
	mi, cont := NewMatchIter(this, r.GetParts()[1], EmptyPD(), es)
	for cont {
		res, matches, done := mi.next()
		cont = !done
		if res {
			replacedRhs := ReplacePD(r.GetParts()[2], es, matches)
			toReturn, ok := tryCondWithMatches(replacedRhs, matches, es)
			if ok {
				return toReturn, true
			}
		}
	}
	return this, false
}
