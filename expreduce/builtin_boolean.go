package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func GetBooleanDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "And",
		toString: func(this *expreduceapi.Expression, params expreduceapi.ToStringParams) (bool, string) {
			return ToStringInfix(this.Parts[1:], " && ", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			res := NewExpression([]expreduceapi.Ex{NewSymbol("System`And")})
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
					if falseQ(this.Parts[i], &es.CASLogger) {
						return NewSymbol("System`False")
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return NewSymbol("System`True")
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Or",
		toString: func(this *expreduceapi.Expression, params expreduceapi.ToStringParams) (bool, string) {
			return ToStringInfix(this.Parts[1:], " || ", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			res := NewExpression([]expreduceapi.Ex{NewSymbol("System`Or")})
			for i := 1; i < len(this.Parts); i++ {
				this.Parts[i] = this.Parts[i].Eval(es)
				if booleanQ(this.Parts[i], &es.CASLogger) {
					if trueQ(this.Parts[i], &es.CASLogger) {
						return NewSymbol("System`True")
					}
				} else {
					res.appendEx(this.Parts[i])
				}
			}
			if len(res.Parts) == 1 {
				return NewSymbol("System`False")
			}
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Not",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			if trueQ(this.Parts[1], &es.CASLogger) {
				return NewSymbol("System`False")
			}
			if falseQ(this.Parts[1], &es.CASLogger) {
				return NewSymbol("System`True")
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name:         "TrueQ",
		legacyEvalFn: singleParamQLogEval(trueQ),
	})
	defs = append(defs, Definition{
		Name:         "BooleanQ",
		legacyEvalFn: singleParamQLogEval(booleanQ),
	})
	defs = append(defs, Definition{Name: "AllTrue"})
	defs = append(defs, Definition{Name: "Boole"})
	return
}
