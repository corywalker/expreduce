package expreduce

import (
	"math/big"
	"time"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getTimeDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "UnixTime",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 1 {
				return this
			}

			return atoms.NewInteger(big.NewInt(time.Now().UTC().Unix()))
		},
	})
	defs = append(defs, Definition{
		Name: "Pause",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			nInt, nIsInt := this.GetParts()[1].(*atoms.Integer)
			nFlt, nIsFlt := this.GetParts()[1].(*atoms.Flt)
			if !nIsInt && !nIsFlt {
				return this
			}
			var duration time.Duration
			if nIsInt {
				duration = time.Duration(nInt.Val.Int64() * 1000000000)
			}
			if nIsFlt {
				asFlt, _ := nFlt.Val.Float64()
				duration = time.Duration(asFlt * 1000000000)
			}
			time.Sleep(duration)
			return atoms.NewSymbol("System`Null")
		},
	})
	return
}
