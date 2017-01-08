package expreduce

import (
	"sort"
)

func GetSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Sort",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			exp, ok := this.Parts[1].(*Expression)
			if ok {
				sort.Sort(exp)
				return exp
			}
			return this
		},
	})
	return
}
