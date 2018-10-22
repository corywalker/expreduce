package matcher

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func ReplacePDInternal(e expreduceapi.Ex, pm *PDManager) (expreduceapi.Ex, bool) {
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
		if atoms.ContainsSymbol(this, k) {
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
