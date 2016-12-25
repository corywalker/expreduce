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

func permListContains(permList [][]Ex, perm []Ex, cl *CASLogger) bool {
	for _, permInList := range permList {
		if len(permInList) != len(perm) {
			continue
		}
		same := true
		for i := range perm {
			if !IsSameQ(perm[i], permInList[i], cl) {
				same = false
				//break
			}
		}
		if same {
			return true
		}
	}
	return false
}

func GenPermutations(parts []Ex, cl *CASLogger) (perms [][]Ex) {
	// Base case
	if len(parts) == 1 {
		return [][]Ex{parts}
	}
	// Recursion
	toReturn := [][]Ex{}
	for i, first := range parts {
		// We must make a copy of "parts" becasue selecting "others" actually
		// modifies "parts" and corrupts it.
		copyParts := make([]Ex, len(parts))
		copy(copyParts, parts)
		others := append(copyParts[:i], copyParts[i+1:]...)
		// TODO: This might be bad for memory complexity.
		otherPerms := GenPermutations(others, cl)
		for _, perm := range otherPerms {
			prepended := make([]Ex, len(perm))
			copy(prepended, perm)
			perm  = append([]Ex{first}, perm...)
			// TODO: And this is bad for time complexity:
			if !permListContains(toReturn, perm, cl) {
				toReturn = append(toReturn, perm)
			}
		}
	}
	return toReturn
}

func (this *Expression) EvalPermutations(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	list, listIsExpr := this.Parts[1].(*Expression)
	if !listIsExpr {
		return this
	}

	perms := GenPermutations(list.Parts[1:], &es.CASLogger)

	exPerms := &Expression{[]Ex{&Symbol{"List"}}}
	for _, perm := range perms {
		toAppend := &Expression{[]Ex{&Symbol{"List"}}}
		for _, ex := range perm {
			toAppend.Parts = append(toAppend.Parts, ex)
		}
		exPerms.Parts = append(exPerms.Parts, toAppend)
	}

	return exPerms
}
