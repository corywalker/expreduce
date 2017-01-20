package expreduce

import (
	"sort"
)

func IterableReplace(components *[]Ex, r *Expression, pm *PDManager, cl *CASLogger) {
	pm = CopyPD(pm)
	for i := range *components {
		cl.Debugf("Attempting IsMatchQ(%s, %s, %s)", (*components)[i], r.Parts[1], pm)
		if res, _ := IsMatchQ((*components)[i], r.Parts[1], pm, cl); res {
			(*components)[i] = r.Parts[2].DeepCopy()
			cl.Debugf("IsMatchQ succeeded, new components: %s", ExArrayToString(*components))
		}
	}
}

func OrderlessReplace(components *[]Ex, lhs_components []Ex, rhs Ex, cl *CASLogger) {
	// TODO: Doesn't take a PDManager as an input right now. Will add this later.
	cl.Infof("Entering OrderlessReplace(components: *%s, lhs_components: %s)", ExArrayToString(*components), ExArrayToString(lhs_components))
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
			mq, matches := IsMatchQ((*components)[perm[i]].DeepCopy(), lhs_components[i], pm, cl)
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
					*components = append(*components, []Ex{ReplacePD(rhs.DeepCopy(), cl, matches)}...)
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
