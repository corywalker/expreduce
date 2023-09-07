package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// Used for the IntegerPartitions builtin
func genIntegerPartitions(
	n int,
	k int,
	startAt int,
	prefix []int,
	parts *[][]int,
) {
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
			genIntegerPartitions(n-i, k, min(i, n-i), prefix, parts)
		}
	}
}

// Used for the Permutations builtin
func permListContains(
	permList [][]expreduceapi.Ex,
	perm []expreduceapi.Ex,
	cl expreduceapi.LoggingInterface,
) bool {
	for _, permInList := range permList {
		if len(permInList) != len(perm) {
			continue
		}
		same := true
		for i := range perm {
			if !atoms.IsSameQ(perm[i], permInList[i]) {
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
func genPermutations(
	parts []expreduceapi.Ex,
	cl expreduceapi.LoggingInterface,
) (perms [][]expreduceapi.Ex) {
	// Base case
	if len(parts) == 1 {
		return [][]expreduceapi.Ex{parts}
	}
	// Recursion
	toReturn := [][]expreduceapi.Ex{}
	for i, first := range parts {
		// We must make a copy of "parts" because selecting "others" actually
		// modifies "parts" and corrupts it.
		copyParts := make([]expreduceapi.Ex, len(parts))
		copy(copyParts, parts)
		others := append(copyParts[:i], copyParts[i+1:]...)
		// TODO: This might be bad for memory complexity.
		otherPerms := genPermutations(others, cl)
		for _, perm := range otherPerms {
			prepended := make([]expreduceapi.Ex, len(perm))
			copy(prepended, perm)
			perm = append([]expreduceapi.Ex{first}, perm...)
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
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 && len(this.GetParts()) != 3 {
				return this
			}

			n, nIsInt := this.GetParts()[1].(*atoms.Integer)
			if !nIsInt {
				return this
			}
			nnumMachine := int(n.Val.Int64())

			knumMachine := nnumMachine
			if len(this.GetParts()) == 3 {
				k, knumIsInt := this.GetParts()[2].(*atoms.Integer)
				if !knumIsInt {
					return this
				}
				knumMachine = int(k.Val.Int64())
			}

			cmpVal := n.Val.Cmp(big.NewInt(0))
			if cmpVal == -1 {
				return atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
			} else if cmpVal == 0 {
				return atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`List"), atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`List")})})
			}

			var parts [][]int
			genIntegerPartitions(
				nnumMachine,
				knumMachine,
				nnumMachine,
				[]int{},
				&parts,
			)

			exParts := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
			for _, partition := range parts {
				toAppend := atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
				for _, integer := range partition {
					toAppend.AppendEx(
						atoms.NewInteger(big.NewInt(int64(integer))),
					)
				}
				exParts.AppendEx(toAppend)
			}

			return exParts
		},
	})
	defs = append(defs, Definition{
		Name: "Permutations",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			list, listIsExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if !listIsExpr {
				return this
			}

			perms := genPermutations(list.GetParts()[1:], es.GetLogger())

			exPerms := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
			for _, perm := range perms {
				toAppend := atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				)
				for _, ex := range perm {
					toAppend.AppendEx(ex)
				}
				exPerms.AppendEx(toAppend)
			}

			return exPerms
		},
	})
	defs = append(defs, Definition{
		Name: "Multinomial",
	})
	defs = append(defs, Definition{
		Name: "Factorial",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			asInt, isInt := this.GetParts()[1].(*atoms.Integer)
			if isInt {
				if asInt.Val.Cmp(big.NewInt(0)) == -1 {
					return atoms.NewSymbol("System`ComplexInfinity")
				}
				return atoms.NewInteger(factorial(asInt.Val))
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Tuples",
	})
	return
}
