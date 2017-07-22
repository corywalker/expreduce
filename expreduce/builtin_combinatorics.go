package expreduce

import (
	"math/big"
)

// Used for the IntegerPartitions builtin
func genIntegerPartitions(n int, k int, startAt int, prefix []int, parts *[][]int) {
	if len(prefix)+1 > k {
		return
	}
	prefix = append(prefix, 0)
	for i := startAt; i > 0; i-- {
		prefix[len(prefix)-1] = i
		if i == n {
			*parts = append(*parts, make([]int, len(prefix)))
			copy((*parts)[len(*parts)-1], prefix)
		} else {
			genIntegerPartitions(n-i, k, Min(i, n-i), prefix, parts)
		}
	}
}

// Used for the Permutations builtin
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

// Used for the Permutations builtin
func genPermutations(parts []Ex, cl *CASLogger) (perms [][]Ex) {
	// Base case
	if len(parts) == 1 {
		return [][]Ex{parts}
	}
	// Recursion
	toReturn := [][]Ex{}
	for i, first := range parts {
		// We must make a copy of "parts" because selecting "others" actually
		// modifies "parts" and corrupts it.
		copyParts := make([]Ex, len(parts))
		copy(copyParts, parts)
		others := append(copyParts[:i], copyParts[i+1:]...)
		// TODO: This might be bad for memory complexity.
		otherPerms := genPermutations(others, cl)
		for _, perm := range otherPerms {
			prepended := make([]Ex, len(perm))
			copy(prepended, perm)
			perm = append([]Ex{first}, perm...)
			// TODO: And this is bad for time complexity:
			if !permListContains(toReturn, perm, cl) {
				toReturn = append(toReturn, perm)
			}
		}
	}
	return toReturn
}

// Used for the Factorial builtin
func factorial(n *big.Int) (result *big.Int) {
	result = new(big.Int)

	switch n.Cmp(&big.Int{}) {
	case -1, 0:
		result.SetInt64(1)
	default:
		result.Set(n)
		var one big.Int
		one.SetInt64(1)
		result.Mul(result, factorial(n.Sub(n, &one)))
	}
	return
}

func getCombinatoricsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "IntegerPartitions",
		Usage: "`IntegerPartitions[n]` lists the possible ways to partition `n` into smaller integers.\n\n" +
			"`IntegerPartitions[n, k]` lists the possible ways to partition `n` into smaller integers, using up to `k` elements.",
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
				return NewExpression([]Ex{&Symbol{"System`List"}})
			} else if cmpVal == 0 {
				return NewExpression([]Ex{&Symbol{"System`List"}, NewExpression([]Ex{&Symbol{"System`List"}})})
			}

			var parts [][]int
			genIntegerPartitions(nMachine, kMachine, nMachine, []int{}, &parts)

			exParts := NewExpression([]Ex{&Symbol{"System`List"}})
			for _, partition := range parts {
				toAppend := NewExpression([]Ex{&Symbol{"System`List"}})
				for _, integer := range partition {
					toAppend.Parts = append(toAppend.Parts, &Integer{big.NewInt(int64(integer))})
				}
				exParts.Parts = append(exParts.Parts, toAppend)
			}

			return exParts
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Find the partitions of 4:"},
			&SameTest{"{{4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1}}", "IntegerPartitions[4]"},
			&TestComment{"Find the partitions of 10, using a maximum of k = 2 integers:"},
			&SameTest{"{{10}, {9, 1}, {8, 2}, {7, 3}, {6, 4}, {5, 5}}", "IntegerPartitions[10, 2]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"The partitions of zero is a nested empty List:"},
			&SameTest{"{{}}", "IntegerPartitions[0]"},
		},
		Tests: []TestInstruction{
			&SameTest{"{{1}}", "IntegerPartitions[1]"},
			&SameTest{"{}", "IntegerPartitions[-1]"},
			&SameTest{"{}", "IntegerPartitions[-5]"},
			&SameTest{"IntegerPartitions[.5]", "IntegerPartitions[.5]"},
			// With k
			&SameTest{"{{10}}", "IntegerPartitions[10, 1]"},
			&SameTest{"{}", "IntegerPartitions[10, 0]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Permutations",
		Usage: "`Permutations[list]` lists the possible permutations for a given list.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			list, listIsExpr := this.Parts[1].(*Expression)
			if !listIsExpr {
				return this
			}

			perms := genPermutations(list.Parts[1:], &es.CASLogger)

			exPerms := NewExpression([]Ex{&Symbol{"System`List"}})
			for _, perm := range perms {
				toAppend := NewExpression([]Ex{&Symbol{"System`List"}})
				for _, ex := range perm {
					toAppend.Parts = append(toAppend.Parts, ex)
				}
				exPerms.Parts = append(exPerms.Parts, toAppend)
			}

			return exPerms
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Find the permutations of `{1, 2, 3}`:"},
			&SameTest{"{{1, 2, 3}, {1, 3, 2}, {2, 1, 3}, {2, 3, 1}, {3, 1, 2}, {3, 2, 1}}", "Permutations[Range[3]]"},
			&TestComment{"`Permutations` ignores duplicates:"},
			&SameTest{"{{1, 2, 2}, {2, 1, 2}, {2, 2, 1}}", "Permutations[{1, 2, 2}]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Multinomial",
		Usage:      "`Multinomial[n1, n2, ...]` gives the multinomial coefficient for the given term.",
		Attributes: []string{"Listable", "NumericFunction", "Orderless", "ReadProtected"},
		Rules: []Rule{
			{"Multinomial[seq___]", "Factorial[Apply[Plus, {seq}]] / Apply[Times, Map[Factorial, {seq}]]"},
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Find the multinomial coefficient for the 1, 3, 1 term:"},
			&SameTest{"20", "Multinomial[1, 3, 1]"},
			&TestComment{"`Multinomial` handles symbolic arguments:"},
			&SameTest{"Factorial[k+2] / Factorial[k]", "Multinomial[1,k,1]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Factorial",
		Usage:      "`n!` returns the factorial of `n`.",
		Attributes: []string{"Listable", "NumericFunction", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			asInt, isInt := this.Parts[1].(*Integer)
			if isInt {
				if asInt.Val.Cmp(big.NewInt(0)) == -1 {
					return &Symbol{"System`ComplexInfinity"}
				}
				return &Integer{factorial(asInt.Val)}
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"2432902008176640000", "20!"},
			&SameTest{"120", "Factorial[5]"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"1", "Factorial[0]"},
			&SameTest{"ComplexInfinity", "Factorial[-1]"},
		},
		Tests: []TestInstruction{
			&SameTest{"1", "Factorial[1]"},
			&SameTest{"1", "Factorial[0]"},
			&SameTest{"1", "Factorial[-0]"},
			&SameTest{"ComplexInfinity", "Factorial[-10]"},
			&SameTest{"120", "Factorial[5]"},

			&SameTest{"Indeterminate", "0 * Infinity"},
			&SameTest{"Indeterminate", "0 * ComplexInfinity"},
		},
	})
	return
}
