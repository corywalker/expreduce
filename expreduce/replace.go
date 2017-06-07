package expreduce

import (
	"sort"
	"math"
)

func OrderlessReplace(components *[]Ex, lhs_components []Ex, rhs Ex, dm *DefMap, cl *CASLogger) {
	GeneralReplace(components, lhs_components, rhs, true, false, "", dm, cl)
	return
	// TODO: Doesn't take a PDManager as an input right now. Will add this later.
	cl.Debugf("Entering OrderlessReplace(components: *%s, lhs_components: %s)", ExArrayToString(*components), ExArrayToString(lhs_components))
	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(*components))
	for i := range toPermute {
		toPermute[i] = i
	}
	//TODO: convert this to nextKPermutation?
	perms := permutations(toPermute, len(lhs_components))
	cl.Debugf("Permutations to try: %v\n", perms)

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		pm := EmptyPD()
		//cl.Debugf("Before snapshot. Context: %v\n", es)
		for i := range perm {
			//cl.Debugf("%s %s\n", (*components)[perm[i]], lhs_components[i])
			mq, matches := IsMatchQ((*components)[perm[i]].DeepCopy(), lhs_components[i], dm, pm, cl)
			if mq {
				pm.Update(matches)
				used[pi] = perm[i]
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					cl.Debugf("About to delete components matching lhs.")
					cl.Debugf("components before: %s", ExArrayToString(*components))
					for tdi, todelete := range used {
						*components = append((*components)[:todelete-tdi], (*components)[todelete-tdi+1:]...)
					}
					cl.Debugf("components after: %s", ExArrayToString(*components))
					cl.Debugf("Appending %s\n", rhs)
					//cl.Debugf("Context: %v\n", es)
					*components = append(*components, []Ex{ReplacePD(rhs.DeepCopy(), dm, cl, matches)}...)
					cl.Debugf("components after append: %s", ExArrayToString(*components))
					//cl.Debugf("After clear. Context: %v\n", es)
					return
				}
			}
			//cl.Debugf("Done checking. Context: %v\n", es)
		}
		//cl.Debugf("After clear. Context: %v\n", es)
	}
}

func allRuns(totLength int) [][]int {
	// Example: allRuns(3) == [[0 1 2] [0 1] [1 2] [0] [1] [2]]
	res := make([][]int, 0)
	for thisLen := totLength; thisLen > 0; thisLen -= 1 {
		for startI := 0; startI <= (totLength-thisLen); startI += 1 {
			thisRun := []int{}
			for i := 0; i < thisLen; i++ {
				thisRun = append(thisRun, i+startI)
			}
			res = append(res, thisRun)
		}
	}
	return res
}

func powerset(n int) [][]int {
	p := make([][]int, 0)
	c := int(math.Pow(2, float64(n)))
	for j := 1; j < c; j++ {
		ss := make([]int, 0)
		for k := 0; k < n; k++ {
			flag := 1 << uint(k)
			if (j)&flag == flag {
				ss = append(ss, k)
			}
		}
		p = append(p, ss)
	}
	return p
}

func FlatReplace(components *[]Ex, lhs_components []Ex, rhs Ex, sequenceHead string, dm *DefMap, cl *CASLogger) {
	GeneralReplace(components, lhs_components, rhs, false, true, sequenceHead, dm, cl)
}

func GeneralReplace(components *[]Ex, lhs_components []Ex, rhs Ex, isOrderless bool, isFlat bool, sequenceHead string, dm *DefMap, cl *CASLogger) {
	// TODO: Doesn't take a PDManager as an input right now. Will add this later.
	cl.Debugf("Entering FlatReplace(components: *%s, lhs_components: %s)", ExArrayToString(*components), ExArrayToString(lhs_components))
	//TODO: convert to a generator method?
	var runs [][]int
	if isOrderless && isFlat {
		runs = powerset(len(*components))
	} else if isOrderless && !isFlat {
		allIndices := []int{}
		for i := 0; i < len(*components); i++ {
			allIndices = append(allIndices, i)
		}
		runs = append(runs, allIndices)
	} else {
		runs = allRuns(len(*components))
	}
	cl.Debugf("Runs to try: %v\n", runs)

	for _, run := range runs {
		thisComponents := make([]Ex, len(run))
		for tci, ci := range run {
			thisComponents[tci] = (*components)[ci].DeepCopy()
		}
		pm := EmptyPD()
		mq, matches := ComponentsIsMatchQ(thisComponents, lhs_components, isOrderless, isFlat, sequenceHead, dm, pm, cl)
		if mq {
			if isOrderless && isFlat {
				sort.Ints(run)
				for tdi, todelete := range run {
					*components = append((*components)[:todelete-tdi], (*components)[todelete-tdi+1:]...)
				}
				*components = append(*components, []Ex{ReplacePD(rhs.DeepCopy(), dm, cl, matches)}...)
			} else {
				copiedComponents := ExArrayDeepCopy((*components)[run[len(run)-1]+1:])
				*components = append((*components)[:run[0]], []Ex{ReplacePD(rhs.DeepCopy(), dm, cl, matches)}...)
				*components = append(*components, copiedComponents...)
			}
			return
		}
		//cl.Debugf("Done checking. Context: %v\n", es)
	}
}

func ReplacePD(this Ex, dm *DefMap, cl *CASLogger, pm *PDManager) Ex {
	cl.Debugf("In ReplacePD(%v, pm=%v)", this, pm)
	toReturn := this.DeepCopy()
	// In Golang, map iterations present random order. In rare circumstances,
	// this can lead to different return expressions for the same inputs
	// causing inconsistency, and random issues with test cases. We want
	// deteriministic return values from this function (and most all functions,
	// for that matter), so we first sort the keys alphabetically.

	// An expression which used to exhibit this indeterminate behavior can be
	// found on line 68 of simplify_test.go at commit 1a7ca11. It would
	// occasionally return 16 instead of m^2 given the input of m^2*m^2. My
	// guess is that one of the simplify patterns has a match object named "m",
	// but I could be wrong.

	// Isolating this issue might help me debug the issue where patterns can
	// interfere with existing variable names. TODO: Look into this.
	keys := []string{}
	for k := range pm.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	// First add a "UniqueDefined`" prefix to each pattern name. This will avoid
	// Any issues where the pattern name is also a variable in one of the
	// pattern definitions. For example, foo[k_, m_] := bar[k, m] and calling
	// foo[m, 2] might print bar[2, 2] without this change.
	for _, nameStr := range keys {
		toReturn = ReplaceAll(toReturn,
			NewExpression([]Ex{
				&Symbol{"Rule"},
				&Symbol{nameStr},
				&Symbol{"UniqueDefined`" + nameStr},
			}),

			dm, cl, EmptyPD(), "")
	}
	for _, nameStr := range keys {
		def := pm.patternDefined[nameStr]
		toReturn = ReplaceAll(toReturn,
			NewExpression([]Ex{
				&Symbol{"Rule"},
				&Symbol{"UniqueDefined`" + nameStr},
				def,
			}),

			dm, cl, EmptyPD(), "")
	}
	cl.Debugf("Finished ReplacePD with toReturn=%v", toReturn)
	return toReturn
}

// The goal of this function is to replace all matching expressions with the
// RHS upon successful matches. We will NOT substitute any named patterns in
// the RHS. We will merely make sure that the named patterns are added to pm.
// Final named pattern substitution will occur at the last possible time.
func ReplaceAll(this Ex, r *Expression, dm *DefMap, cl *CASLogger, pm *PDManager,
                stopAtHead string) Ex {
	_, isFlt := this.(*Flt)
	_, isInteger := this.(*Integer)
	_, isString := this.(*String)
	asExpression, isExpression := this.(*Expression)
	_, isSymbol := this.(*Symbol)
	_, isRational := this.(*Rational)

	if isFlt || isInteger || isString || isSymbol || isRational {
		if res, matches := IsMatchQ(this, r.Parts[1], dm, pm, cl); res {
			return ReplacePD(r.Parts[2], dm, cl, matches)
		}
		return this
	} else if isExpression {
		_, isRestrictedHead := HeadAssertion(this, stopAtHead)
		if isRestrictedHead {
			return this
		} else {
			// Continue recursion
			cl.Debugf("ReplaceAll(%v, %v, es, %v)", this, r, pm)
			return asExpression.ReplaceAll(r, cl, stopAtHead, dm)
		}
	}
	return &Symbol{"$ReplaceAllFailed"}
}

func permutations(iterable []int, r int) [][]int {
	res := make([][]int, 0)
	pool := iterable
	n := len(pool)

	if r > n {
		return res
	}

	indices := make([]int, n)
	for i := range indices {
		indices[i] = i
	}

	cycles := make([]int, r)
	for i := range cycles {
		cycles[i] = n - i
	}

	result := make([]int, r)
	for i, el := range indices[:r] {
		result[i] = pool[el]
	}

	c := make([]int, len(result))
	copy(c, result)
	res = append(res, c)

	for n > 0 {
		i := r - 1
		for ; i >= 0; i -= 1 {
			cycles[i] -= 1
			if cycles[i] == 0 {
				index := indices[i]
				for j := i; j < n-1; j += 1 {
					indices[j] = indices[j+1]
				}
				indices[n-1] = index
				cycles[i] = n - i
			} else {
				j := cycles[i]
				indices[i], indices[n-j] = indices[n-j], indices[i]

				for k := i; k < r; k += 1 {
					result[k] = pool[indices[k]]
				}

				c := make([]int, len(result))
				copy(c, result)
				res = append(res, c)

				break
			}
		}

		if i < 0 {
			return res
		}

	}
	return res

}
