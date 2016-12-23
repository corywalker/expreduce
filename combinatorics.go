package cas

import (
	"math/big"
)

func GenIntegerPartitions(n int, startAt int) (parts [][]int) {
	for i := startAt; i > 0; i-- {
		if i == n {
			parts = append(parts, []int{n})
		} else {
			subparts := GenIntegerPartitions(n-i, Min(i, n-i))
			for _, partition := range subparts {
				parts = append(parts, append([]int{i}, partition...))
			}
		}
	}
	return
}

func (this *Expression) EvalIntegerPartitions(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	n, nIsInt := this.Parts[1].(*Integer)

	if !nIsInt {
		return this
	}

	cmpVal := n.Val.Cmp(big.NewInt(0))
	if cmpVal == -1 {
		return &Expression{[]Ex{&Symbol{"List"}}}
	} else if cmpVal == 0 {
		return &Expression{[]Ex{&Symbol{"List"}, &Expression{[]Ex{&Symbol{"List"}}}}}
	}

	nMachine := int(n.Val.Int64())
	parts := GenIntegerPartitions(nMachine, nMachine)

	exParts := &Expression{[]Ex{&Symbol{"List"}}}
	for _, partition := range parts {
		toAppend := &Expression{[]Ex{&Symbol{"List"}}}
		for _, integer := range partition {
			toAppend.Parts = append(toAppend.Parts, &Integer{big.NewInt(int64(integer))})
		}
		exParts.Parts = append(exParts.Parts, toAppend)
	}

	return exParts
}
