package cas

import (
	"math/big"
)

func GenIntegerPartitions(n int, k int, startAt int, prefix []int, parts *[][]int) {
	if len(prefix) + 1 > k {
		return
	}
	prefix = append(prefix, 0)
	for i := startAt; i > 0; i-- {
		prefix[len(prefix)-1] = i
		if i == n {
			*parts = append(*parts, make([]int, len(prefix)))
			copy((*parts)[len(*parts)-1], prefix)
		} else {
			GenIntegerPartitions(n-i, k, Min(i, n-i), prefix, parts)
		}
	}
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

func GetCombinatoricsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "IntegerPartitions",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
	if len(this.Parts) != 2 && len(this.Parts) != 3 {
		return this
	}

	n, nIsInt := this.Parts[1].(*Integer)
	if !nIsInt {
		return this
	}
	nMachine := int(n.Val.Int64())

	kMachine := nMachine
	if len(this.Parts) == 3 {
		k, kIsInt := this.Parts[2].(*Integer)
		if !kIsInt {
			return this
		}
		kMachine = int(k.Val.Int64())
	}

	cmpVal := n.Val.Cmp(big.NewInt(0))
	if cmpVal == -1 {
		return &Expression{[]Ex{&Symbol{"List"}}}
	} else if cmpVal == 0 {
		return &Expression{[]Ex{&Symbol{"List"}, &Expression{[]Ex{&Symbol{"List"}}}}}
	}

	var parts [][]int
	GenIntegerPartitions(nMachine, kMachine, nMachine, []int{}, &parts)

	exParts := &Expression{[]Ex{&Symbol{"List"}}}
	for _, partition := range parts {
		toAppend := &Expression{[]Ex{&Symbol{"List"}}}
		for _, integer := range partition {
			toAppend.Parts = append(toAppend.Parts, &Integer{big.NewInt(int64(integer))})
		}
		exParts.Parts = append(exParts.Parts, toAppend)
	}

	return exParts
		},
	})
	defs = append(defs, Definition{
		name: "Permutations",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		},
	})
	return
}
