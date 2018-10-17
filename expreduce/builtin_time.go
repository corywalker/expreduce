package expreduce

import (
	"math/big"
	"time"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func GetTimeDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "UnixTime",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 1 {
				return this
			}

			return NewInteger(big.NewInt(time.Now().UTC().Unix()))
		},
	})
	defs = append(defs, Definition{
		Name: "Pause",
		legacyEvalFn: func(this *expreduceapi.ExpressionInterface, es *expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}
			nInt, nIsInt := this.Parts[1].(*Integer)
			nFlt, nIsFlt := this.Parts[1].(*Flt)
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
			return NewSymbol("System`Null")
		},
	})
	return
}
