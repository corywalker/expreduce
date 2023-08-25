package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getBooleanDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "And",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfix(this.GetParts()[1:], " && ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`And")},
			)
			for i := 1; i < len(this.GetParts()); i++ {
				this.GetParts()[i] = es.Eval(this.GetParts()[i])
				if booleanQ(this.GetParts()[i], es.GetLogger()) {
					if falseQ(this.GetParts()[i], es.GetLogger()) {
						return atoms.NewSymbol("System`False")
					}
				} else {
					res.AppendEx(this.GetParts()[i])
				}
			}
			if len(res.GetParts()) == 1 {
				return atoms.NewSymbol("System`True")
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
			return toStringInfix(this.GetParts()[1:], " || ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`Or")},
			)
			for i := 1; i < len(this.GetParts()); i++ {
				this.GetParts()[i] = es.Eval(this.GetParts()[i])
				if booleanQ(this.GetParts()[i], es.GetLogger()) {
					if trueQ(this.GetParts()[i], es.GetLogger()) {
						return atoms.NewSymbol("System`True")
					}
				} else {
					res.AppendEx(this.GetParts()[i])
				}
			}
			if len(res.GetParts()) == 1 {
				return atoms.NewSymbol("System`False")
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
			if trueQ(this.GetParts()[1], es.GetLogger()) {
				return atoms.NewSymbol("System`False")
			}
			if falseQ(this.GetParts()[1], es.GetLogger()) {
				return atoms.NewSymbol("System`True")
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
