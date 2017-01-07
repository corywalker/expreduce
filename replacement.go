package cas

import "sort"

func ReplacePD(this Ex, cl *CASLogger, pm *PDManager) Ex {
	cl.Infof("In ReplacePD(%v, pm=%v)", this, pm)
	toReturn := this.DeepCopy()
	// In Golang, map iterations present random order. In rare circumstances,
	// this can lead to different return expressions for the same inputs
	// causing inconsistency, and random issues with test cases. We want
	// deteriministic return values from this function (and most all functions,
	// for that matter), so we first sort the keys alphabetically.

	// An expression which used to exhibit this indeterminate behavior can be
	// found on line 68 of simplify_test.go at commit 1a7ca11. It would
	// occasionally return 16 instead of m^2 given the input of m^2*m^2. My
	// guess is that one of the simplify patterns has a match object named "m",
	// but I could be wrong.

	// Isolating this issue might help me debug the issue where patterns can
	// interfere with existing variable names. TODO: Look into this.
	keys := []string{}
	for k, _ := range pm.patternDefined { keys = append(keys,k) }
	sort.Strings(keys)
	// First add a "UniqueDefined`" prefix to each pattern name. This will avoid
	// Any issues where the pattern name is also a variable in one of the
	// pattern definitions. For example, foo[k_, m_] := bar[k, m] and calling
	// foo[m, 2] might print bar[2, 2] without this change.
	for _, nameStr := range keys {
		toReturn = ReplaceAll(toReturn,
			&Expression{[]Ex{
				&Symbol{"Rule"},
				&Symbol{nameStr},
				&Symbol{"UniqueDefined`" + nameStr},
			}}, cl, EmptyPD())
	}
	for _, nameStr := range keys {
		def := pm.patternDefined[nameStr]
		toReturn = ReplaceAll(toReturn,
			&Expression{[]Ex{
				&Symbol{"Rule"},
				&Symbol{"UniqueDefined`" + nameStr},
				def,
			}}, cl, EmptyPD())
	}
	cl.Infof("Finished ReplacePD with toReturn=%v", toReturn)
	return toReturn
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func ReplaceAll(this Ex, r *Expression, cl *CASLogger, pm *PDManager) Ex {
	_, isFlt := this.(*Flt)
	_, isInteger := this.(*Integer)
	_, isString := this.(*String)
	asExpression, isExpression := this.(*Expression)
	_, isSymbol := this.(*Symbol)
	_, isRational := this.(*Rational)

	if isFlt || isInteger || isString || isSymbol || isRational {
		if res, matches := IsMatchQ(this, r.Parts[1], pm, cl); res {
			return ReplacePD(r.Parts[2], cl, matches)
		}
		return this
	} else if isExpression {
		cl.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
		return asExpression.ReplaceAll(r, cl)
	}
	return &Symbol{"ReplaceAllFailed"}
}

func GetReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "ReplaceAll",
		toString: func (this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " /. ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
			if !ok {
				rulesRule, ok = HeadAssertion(this.Parts[2], "RuleDelayed")
			}
			if ok {
				newEx := ReplaceAll(this.Parts[1], rulesRule, &es.CASLogger, EmptyPD())
				return newEx.Eval(es)
			}

			// Also handle a list of Rules
			asList, isList := HeadAssertion(this.Parts[2], "List")
			if isList {
				toReturn := this.Parts[1]
				for i := 1; i < len(asList.Parts); i++ {
					rulesRule, ok := HeadAssertion(asList.Parts[i], "Rule")
					if !ok {
						rulesRule, ok = HeadAssertion(asList.Parts[i], "RuleDelayed")
					}
					if ok {
						toReturn = ReplaceAll(toReturn.DeepCopy(), rulesRule, &es.CASLogger, EmptyPD())
					}
				}
				return toReturn.Eval(es)
			}

			return this
		},
	})
	defs = append(defs, Definition{
		name: "ReplaceRepeated",
		toString: func (this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " //. ", true, "", "", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			es.Infof("Starting ReplaceRepeated.")
			isSame := false
			oldEx := this.Parts[1]
			es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
			for !isSame {
				newEx := (&Expression{[]Ex{
					&Symbol{"ReplaceAll"},
					oldEx.DeepCopy(),
					this.Parts[2],
				}}).Eval(es)
				//newEx = newEx.Eval(es)
				es.Infof("In ReplaceRepeated. New expr: %v", newEx)

				if IsSameQ(oldEx, newEx, &es.CASLogger) {
					isSame = true
				}
				oldEx = newEx
			}
			return oldEx
		},
	})
	defs = append(defs, Definition{
		name: "Rule",
		toString: func (this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " -> ", true, "", "", form)
		},
	})
	defs = append(defs, Definition{
		name: "RuleDelayed",
		toString: func (this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " :> ", true, "", "", form)
		},
	})
	return
}
