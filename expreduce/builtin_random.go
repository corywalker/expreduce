package expreduce

import (
	"math/big"
	"math/rand"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getRandomDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "RandomReal",
		Details: "`SeedRandom[UnixTime[]]` is called automatically upon " +
			"initialization of Expreduce, so random number sequences will not " +
			"repeat over subsequent sessions.",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 1 {
				return this
			}

			return atoms.NewReal(big.NewFloat(rand.Float64()))
		},
	})
	defs = append(defs, Definition{
		Name: "SeedRandom",
		Details: "`SeedRandom[UnixTime[]]` is called automatically upon " +
			"initialization of Expreduce, so random number sequences will not " +
			"repeat over subsequent sessions.",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			asInt, isInt := this.GetParts()[1].(*atoms.Integer)
			if isInt {
				//nolint:staticcheck
				rand.Seed(asInt.Val.Int64())
				return atoms.NewSymbol("System`Null")
			}

			return this
		},
	})
	return
}
