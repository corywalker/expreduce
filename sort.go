package cas

import (
	"sort"
)

func (this *Expression) EvalSort(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	exp, ok := this.Parts[1].(*Expression)
	if ok {
		sort.Sort(exp)
		return exp
	}
	return this
}
