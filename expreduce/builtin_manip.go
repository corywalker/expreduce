package expreduce

func distribute(e *Expression, built *Expression, res *Expression) {
	i := len(built.Parts)
	if i >= len(e.Parts) {
		res.Parts = append(res.Parts, built)
		return
	}
	shouldDistribute := false
	partAsExpr, partIsExpr := e.Parts[i].(*Expression)
	if partIsExpr {
		if hashEx(partAsExpr.Parts[0]) == hashEx(res.Parts[0]) {
			shouldDistribute = true
		}
	}
	if shouldDistribute {
		for _, dPart := range(partAsExpr.Parts[1:]) {
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
	defs = append(defs, Definition{
		Name:  "Distribute",
		Rules: []Rule{
			{"Distribute[e_]", "Distribute[e, Plus]"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[1].(*Expression)
			if !isExpr {
				return this.Parts[1]
			}
			res := NewExpression([]Ex{this.Parts[2]})
			firstBuilt := NewExpression([]Ex{expr.Parts[0]})
			distribute(expr, firstBuilt, res)
			return res
		},
	})
	return
}
