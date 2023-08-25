package matcher

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func replacePDInternal(
	e expreduceapi.Ex,
	pm *PDManager,
) (expreduceapi.Ex, bool) {
	asSym, isSym := e.(*atoms.Symbol)
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
			possiblyNewExpr, dirty := replacePDInternal(
				asExpr.GetParts()[i],
				pm,
			)
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

// ReplacePD takes an expression and replaces any defined symbols in the
// PDManager with the defined values. It is a form of subsitution common in
// function evaluation and replacement.
func ReplacePD(
	expr expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
	pm *PDManager,
) expreduceapi.Ex {
	if pm == nil {
		return expr
	}
	containsAny := false
	for k := range pm.patternDefined {
		if atoms.ContainsSymbol(expr, k) {
			containsAny = true
			break
		}
	}
	if !containsAny {
		return expr
	}

	// Expressions are immutable. Any time we change an expression, we must
	// first copy it.
	res, _ := replacePDInternal(expr.Copy(), pm)
	return res
}
