package expreduce

import (
	"math"
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func mathFnOneParam(
	fn func(float64) float64,
) func(expreduceapi.ExpressionInterface, expreduceapi.EvalStateInterface) expreduceapi.Ex {
	return (func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
		if len(this.GetParts()) != 2 {
			return this
		}

		flt, ok := this.GetParts()[1].(*atoms.Flt)
		if ok {
			flt64, acc := flt.Val.Float64()
			if acc == big.Exact {
				return atoms.NewReal(big.NewFloat(fn(flt64)))
			}
		}
		return this
	})
}

func getTrigDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:         "Sin",
		legacyEvalFn: mathFnOneParam(math.Sin),
		toString:     simpleTeXToString("sin"),
	})
	defs = append(defs, Definition{
		Name:         "Cos",
		legacyEvalFn: mathFnOneParam(math.Cos),
		toString:     simpleTeXToString("cos"),
	})
	defs = append(defs, Definition{
		Name:         "Tan",
		legacyEvalFn: mathFnOneParam(math.Tan),
		toString:     simpleTeXToString("tan"),
	})
	defs = append(defs, Definition{
		Name:         "ArcTan",
		legacyEvalFn: mathFnOneParam(math.Atan),
		toString:     simpleTeXToString("tan^{-1}"),
	})
	defs = append(defs, Definition{
		Name: "Cot",
		legacyEvalFn: mathFnOneParam(
			func(x float64) float64 { return 1 / math.Tan(x) },
		),
		toString: simpleTeXToString("cot"),
	})
	defs = append(defs, Definition{
		Name:              "TrigExpand",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "TrigReduce",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "TrigToExp",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "Degree"})
	defs = append(defs, Definition{Name: "RotationMatrix"})
	return
}
