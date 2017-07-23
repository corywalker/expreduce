package expreduce

import "math/big"

func GetNumberTheoryDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:         "PrimeQ",
		legacyEvalFn: singleParamQEval(primeQ),
	})
	defs = append(defs, Definition{
		Name: "GCD",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			zero := big.NewInt(0)
			var ints [](*big.Int)
			for i := 1; i < len(this.Parts); i++ {
				asInt, isInt := this.Parts[i].(*Integer)
				if !isInt {
					return this
				}
				r := asInt.Val.Cmp(zero)
				if r > 0 {
					tmpI := big.NewInt(0)
					tmpI.Set(asInt.Val)
					ints = append(ints, tmpI)
				}
				if r < 0 {
					tmpI := big.NewInt(0)
					tmpI.Neg(asInt.Val)
					ints = append(ints, tmpI)
				}
			}
			if len(ints) == 0 {
				return &Integer{zero}
			}
			gcd := ints[0]
			for i := 1; i < len(ints); i++ {
				gcd.GCD(nil, nil, gcd, ints[i])
			}
			return &Integer{gcd}
		},
	})
	defs = append(defs, Definition{Name: "LCM"})
	defs = append(defs, Definition{
		Name: "Mod",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			xi, xIsInt := this.Parts[1].(*Integer)
			yi, yIsInt := this.Parts[2].(*Integer)
			if !xIsInt || !yIsInt {
				return this
			}
			if yi.Val.Cmp(big.NewInt(0)) == 0 {
				return &Symbol{"System`Indeterminate"}
			}
			m := big.NewInt(0)
			m.Mod(xi.Val, yi.Val)
			return &Integer{m}
		},
	})
	defs = append(defs, Definition{Name: "EvenQ"})
	defs = append(defs, Definition{Name: "OddQ"})
	return
}
