package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getAtomsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Rational",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			nAsInt, nIsInt := this.GetParts()[1].(*atoms.Integer)
			dAsInt, dIsInt := this.GetParts()[2].(*atoms.Integer)
			if nIsInt && dIsInt {
				return es.Eval(atoms.NewRational(nAsInt.Val, dAsInt.Val))
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Complex",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			validComplexType := func(e expreduceapi.Ex) bool {
				switch e.(type) {
				case *atoms.Integer:
					return true
				case *atoms.Flt:
					return true
				case *atoms.Rational:
					return true
				default:
					return false
				}
			}
			if validComplexType(this.GetParts()[1]) &&
				validComplexType(this.GetParts()[2]) {
				return es.Eval(
					atoms.NewComplex(this.GetParts()[1], this.GetParts()[2]),
				)
			}
			return this
		},
	})
	defs = append(defs, Definition{Name: "String"})
	defs = append(defs, Definition{Name: "Real"})
	defs = append(defs, Definition{Name: "Integer"})
	defs = append(defs, Definition{Name: "IntegerQ"})
	defs = append(defs, Definition{Name: "Im"})
	defs = append(defs, Definition{Name: "Re"})
	defs = append(defs, Definition{
		Name:              "ReIm",
		OmitDocumentation: true,
		expreduceSpecific: true,
	})
	return
}
