package expreduce

import (
	"math/big"
	"sort"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func GetSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Sort",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 2 {
				return this
			}

			exp, ok := this.Parts[1].(*expreduceapi.Expression)
			if ok {
				sortedExp := exp.DeepCopy().(*expreduceapi.Expression)
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
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			toreturn := ExOrder(this.Parts[1], this.Parts[2])
			return NewInteger(big.NewInt(toreturn))
		},
	})
	return
}
