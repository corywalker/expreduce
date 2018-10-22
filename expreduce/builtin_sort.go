package expreduce

import (
	"math/big"
	"sort"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Sort",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			exp, ok := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if ok {
				sortedExp := exp.DeepCopy().(expreduceapi.ExpressionInterface)
				sortedExp.ClearHashes()
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

			toreturn := atoms.ExOrder(this.GetParts()[1], this.GetParts()[2])
			return atoms.NewInteger(big.NewInt(toreturn))
		},
	})
	return
}
