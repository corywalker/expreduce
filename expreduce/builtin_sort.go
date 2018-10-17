package expreduce

import (
	"math/big"
	"sort"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func GetSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Sort",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			exp, ok := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if ok {
				sortedExp := exp.DeepCopy().(expreduceapi.ExpressionInterface)
				sortedExp.evaledHash = 0
				sortedExp.cachedHash = 0
				sort.Sort(sortedExp)
				return sortedExp
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Order",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			toreturn := ExOrder(this.GetParts()[1], this.GetParts()[2])
			return NewInteger(big.NewInt(toreturn))
		},
	})
	return
}
