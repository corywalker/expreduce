package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func getAtomsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Rational",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			nAsInt, nIsInt := this.GetParts()[1].(*Integer)
			dAsInt, dIsInt := this.GetParts()[2].(*Integer)
			if nIsInt && dIsInt {
				return NewRational(nAsInt.Val, dAsInt.Val).Eval(es)
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
				case *Integer:
					return true
				case *Flt:
					return true
				case *Rational:
					return true
				default:
					return false
				}
			}
			if validComplexType(this.GetParts()[1]) && validComplexType(this.GetParts()[2]) {
				return NewComplex(this.GetParts()[1], this.GetParts()[2]).Eval(es)
			}
			return this
		},
	})
	defs = append(defs, Definition{Name: "String"})
	defs = append(defs, Definition{Name: "Real"})
	defs = append(defs, Definition{Name: "Integer"})
	defs = append(defs, Definition{Name: "IntegerQ"})
	defs = append(defs, Definition{
		Name:              "Im",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
	})
	defs = append(defs, Definition{
		Name:              "Re",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
	})
	return
}
