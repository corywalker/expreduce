package expreduce

func GetBooleanDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "And",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringInfix(this.Parts[1:], " && ", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res := NewExpression([]Ex{&Symbol{"System`And"}})
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
				    if falseQ(this.Parts[i], &es.CASLogger) {
						return &Symbol{"System`False"}
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return &Symbol{"System`True"}
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:       "Or",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringInfix(this.Parts[1:], " || ", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res := NewExpression([]Ex{&Symbol{"System`Or"}})
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
				    if trueQ(this.Parts[i], &es.CASLogger) {
						return &Symbol{"System`True"}
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return &Symbol{"System`False"}
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:       "Not",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			if trueQ(this.Parts[1], &es.CASLogger) {
				return &Symbol{"System`False"}
			}
			if falseQ(this.Parts[1], &es.CASLogger) {
				return &Symbol{"System`True"}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "TrueQ",
		legacyEvalFn: singleParamQLogEval(trueQ),
	})
	defs = append(defs, Definition{
		Name: "BooleanQ",
		legacyEvalFn: singleParamQLogEval(booleanQ),
	})
	defs = append(defs, Definition{Name: "AllTrue"})
	defs = append(defs, Definition{Name: "Boole"})
	return
}
