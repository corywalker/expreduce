package expreduce

import (
	"sort"
)

// This function assumes e and lhs have the same head and that the head is Flat.
func FlatReplace(e *Expression, lhs *Expression, rhs Ex, orderless bool, es *EvalState) {
	looseLhs := NewExpression([]Ex{})
	looseLhs.Parts = append(looseLhs.Parts, lhs.Parts[0])
	if !orderless {
		looseLhs.Parts = append(looseLhs.Parts, NewExpression([]Ex{
			&Symbol{"Pattern"},
			&Symbol{"Expreduce`start"},
			NewExpression([]Ex{&Symbol{"BlankNullSequence"}}),
		}))
	}
	looseLhs.Parts = append(looseLhs.Parts, lhs.Parts[1:]...)
	looseLhs.Parts = append(looseLhs.Parts, NewExpression([]Ex{
		&Symbol{"Pattern"},
		&Symbol{"Expreduce`end"},
		NewExpression([]Ex{&Symbol{"BlankNullSequence"}}),
	}))
	pm := EmptyPD()
	matchq, newPd := IsMatchQ(e, looseLhs, pm, es)
	if matchq {
		var tmpEx Ex
		if orderless {
			tmpEx = ReplacePD(NewExpression([]Ex{
				e.Parts[0],
				rhs,
				&Symbol{"Expreduce`end"},
			}), es, newPd)
		} else {
			tmpEx = ReplacePD(NewExpression([]Ex{
				e.Parts[0],
				&Symbol{"Expreduce`start"},
				rhs,
				&Symbol{"Expreduce`end"},
			}), es, newPd)
		}
		tmpExpr := tmpEx.(*Expression)
		e.Parts = tmpExpr.Parts
	}
}

func ReplacePD(this Ex, es *EvalState, pm *PDManager) Ex {
	es.Debugf("In ReplacePD(%v, pm=%v)", this, pm)
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
	for k := range pm.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	// First add a "UniqueDefined`" prefix to each pattern name. This will avoid
	// Any issues where the pattern name is also a variable in one of the
	// pattern definitions. For example, foo[k_, m_] := bar[k, m] and calling
	// foo[m, 2] might print bar[2, 2] without this change.
	for _, nameStr := range keys {
		toReturn = ReplaceAll(toReturn,
			NewExpression([]Ex{
				&Symbol{"Rule"},
				&Symbol{nameStr},
				&Symbol{"UniqueDefined`" + nameStr},
			}),

			es, EmptyPD(), "")
	}
	for _, nameStr := range keys {
		def := pm.patternDefined[nameStr]
		toReturn = ReplaceAll(toReturn,
			NewExpression([]Ex{
				&Symbol{"Rule"},
				&Symbol{"UniqueDefined`" + nameStr},
				def,
			}),

			es, EmptyPD(), "")
	}
	es.Debugf("Finished ReplacePD with toReturn=%v", toReturn)
	return toReturn
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func ReplaceAll(this Ex, r *Expression, es *EvalState, pm *PDManager,
                stopAtHead string) Ex {
	_, isFlt := this.(*Flt)
	_, isInteger := this.(*Integer)
	_, isString := this.(*String)
	asExpression, isExpression := this.(*Expression)
	_, isSymbol := this.(*Symbol)
	_, isRational := this.(*Rational)

	if isFlt || isInteger || isString || isSymbol || isRational {
		if res, matches := IsMatchQ(this, r.Parts[1], pm, es); res {
			return ReplacePD(r.Parts[2], es, matches)
		}
		return this
	} else if isExpression {
		_, isRestrictedHead := HeadAssertion(this, stopAtHead)
		if isRestrictedHead {
			return this
		} else {
			// Continue recursion
			es.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
			return asExpression.ReplaceAll(r, stopAtHead, es)
		}
	}
	return &Symbol{"$ReplaceAllFailed"}
}
