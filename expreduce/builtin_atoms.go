package expreduce

func getAtomsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Rational",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			nAsInt, nIsInt := this.Parts[1].(*Integer)
			dAsInt, dIsInt := this.Parts[2].(*Integer)
			if nIsInt && dIsInt {
				return NewRational(nAsInt.Val, dAsInt.Val).Eval(es)
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Complex",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			rAsInt, rIsInt := this.Parts[1].(*Integer)
			iAsInt, iIsInt := this.Parts[2].(*Integer)
			if rIsInt && iIsInt {
				return NewComplex(rAsInt.Val, iAsInt.Val).Eval(es)
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
