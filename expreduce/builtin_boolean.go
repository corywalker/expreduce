package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func GetBooleanDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "And",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return ToStringInfix(this.GetParts()[1:], " && ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res := NewExpression([]expreduceapi.Ex{NewSymbol("System`And")})
			for i := 1; i < len(this.GetParts()); i++ {
				this.GetParts()[i] = this.GetParts()[i].Eval(es)
				if booleanQ(this.GetParts()[i], &es.CASLogger) {
					if falseQ(this.GetParts()[i], &es.CASLogger) {
						return NewSymbol("System`False")
					}
				} else {
					res.appendEx(this.GetParts()[i])
				}
			}
			if len(res.GetParts()) == 1 {
				return NewSymbol("System`True")
			}
			if len(res.GetParts()) == 2 {
				return res.GetParts()[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Or",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return ToStringInfix(this.GetParts()[1:], " || ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res := NewExpression([]expreduceapi.Ex{NewSymbol("System`Or")})
			for i := 1; i < len(this.GetParts()); i++ {
				this.GetParts()[i] = this.GetParts()[i].Eval(es)
				if booleanQ(this.GetParts()[i], &es.CASLogger) {
					if trueQ(this.GetParts()[i], &es.CASLogger) {
						return NewSymbol("System`True")
					}
				} else {
					res.appendEx(this.GetParts()[i])
				}
			}
			if len(res.GetParts()) == 1 {
				return NewSymbol("System`False")
			}
			if len(res.GetParts()) == 2 {
				return res.GetParts()[1]
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Not",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			if trueQ(this.GetParts()[1], &es.CASLogger) {
				return NewSymbol("System`False")
			}
			if falseQ(this.GetParts()[1], &es.CASLogger) {
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
