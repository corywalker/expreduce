package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func distribute(e expreduceapi.ExpressionInterface, built expreduceapi.ExpressionInterface, res expreduceapi.ExpressionInterface) {
	i := len(built.Parts)
	if i >= len(e.Parts) {
		res.Parts = append(res.Parts, built)
		return
	}
	shouldDistribute := false
	partAsExpr, partIsExpr := e.Parts[i].(expreduceapi.ExpressionInterface)
	if partIsExpr {
		if hashEx(partAsExpr.Parts[0]) == hashEx(res.Parts[0]) {
			shouldDistribute = true
		}
	}
	if shouldDistribute {
		for _, dPart := range partAsExpr.Parts[1:] {
			builtCopy := built.ShallowCopy()
			builtCopy.appendEx(dPart)
			distribute(e, builtCopy, res)
		}
		return
	}
	built.Parts = append(built.Parts, e.Parts[i])
	distribute(e, built, res)
	return
}

func GetManipDefinitions() (defs []Definition) {
	defs = append(defs, Definition{Name: "Together"})
	defs = append(defs, Definition{Name: "Numerator"})
	defs = append(defs, Definition{Name: "Denominator"})
	defs = append(defs, Definition{
		Name: "Apart",
		// Not fully implemented.
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name: "Distribute",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(expreduceapi.ExpressionInterface)
			if !isExpr {
				return this.Parts[1]
			}
			res := NewExpression([]expreduceapi.Ex{this.Parts[2]})
			firstBuilt := NewExpression([]expreduceapi.Ex{expr.Parts[0]})
			distribute(expr, firstBuilt, res)
			return res
		},
	})
	return
}
