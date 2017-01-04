package cas

import "math/big"
import "math/rand"

func GetRandomDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "RandomReal",
		rules: map[string]string{
			"RandomReal[{minmatch_, maxmatch_}]": "RandomReal[]*(maxmatch - minmatch) + minmatch",
			"RandomReal[maxmatch_]": "RandomReal[]*maxmatch",
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 1 {
				return this
			}

			return &Flt{big.NewFloat(rand.Float64())}
		},
	})
	defs = append(defs, Definition{
		name: "SeedRandom",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			asInt, isInt := this.Parts[1].(*Integer)
			if isInt {
				rand.Seed(asInt.Val.Int64())
				return &Symbol{"Null"}
			}

			return this
		},
	})
	return
}
