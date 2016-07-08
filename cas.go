//go:generate go tool yacc -p Calc -o interp.go interp.y
//go:generate golex -o tokenizer.go tokenizer.l

package cas

import (
	"bytes"
	"github.com/op/go-logging"
	"os"
	"sort"
)

var format = logging.MustStringFormatter(
	`%{color}%{time:15:04:05.000} %{shortfunc} ▶ %{level:.4s} %{id:03x}%{color:reset} %{message}`,
)

type EvalState struct {
	defined        map[string]Ex
	patternDefined map[string]Ex
	log            *logging.Logger
	leveled        logging.LeveledBackend
}

func NewEvalState() *EvalState {
	var es EvalState
	es.defined = make(map[string]Ex)
	es.patternDefined = make(map[string]Ex)

	// Set up logging
	es.log = logging.MustGetLogger("example")
	backend := logging.NewLogBackend(os.Stderr, "", 0)
	formatter := logging.NewBackendFormatter(backend, format)
	es.leveled = logging.AddModuleLevel(formatter)
	logging.SetBackend(es.leveled)
	es.DebugOff()

	return &es
}

func (this *EvalState) DebugOn() {
	this.leveled.SetLevel(logging.DEBUG, "")
}

func (this *EvalState) DebugOff() {
	this.leveled.SetLevel(logging.ERROR, "")
}

func (this *EvalState) ClearAll() {
	this.defined = make(map[string]Ex)
	this.patternDefined = make(map[string]Ex)
}

func (this *EvalState) ClearPD() {
	this.patternDefined = make(map[string]Ex)
}

func (this *EvalState) GetDefinedSnapshot() map[string]Ex {
	oldVars := make(map[string]Ex)
	for k, v := range this.defined {
		oldVars[k] = v
	}
	return oldVars
}

func (this *EvalState) ToString() string {
	var buffer bytes.Buffer
	for k, v := range this.defined {
		buffer.WriteString(k)
		buffer.WriteString(": ")
		buffer.WriteString(v.ToString())
		buffer.WriteString("\n")
	}
	for k, v := range this.defined {
		buffer.WriteString(k)
		buffer.WriteString("_: ")
		buffer.WriteString(v.ToString())
		buffer.WriteString("\n")
	}
	return buffer.String()
}

// Ex stands for Expression. Most structs should implement this
type Ex interface {
	Eval(es *EvalState) Ex
	Replace(r *Rule, es *EvalState) Ex
	ToString() string
	IsEqual(b Ex, es *EvalState) string
	IsSameQ(b Ex, es *EvalState) bool
	// After calling an IsMatchQ and failing, one must clear the patternDefined
	// and restore variables to their original state.
	IsMatchQ(b Ex, es *EvalState) bool
	DeepCopy() Ex
}

// Some utility functions that span multiple files

func ExArrayToString(exArray []Ex) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range exArray {
		buffer.WriteString(e.ToString())
		if i != len(exArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func CommutativeIsEqual(components []Ex, other_components []Ex, es *EvalState) string {
	es.log.Infof("Entering CommutativeIsEqual")
	es.log.Infof("components: %s", ExArrayToString(components))
	es.log.Infof("other_components: %s", ExArrayToString(other_components))
	es.log.Debugf("Start of CommutativeIsEqual. Context:\n%v\n", es.ToString())
	if len(components) != len(other_components) {
		return "EQUAL_FALSE"
	}
	matched := make(map[int]struct{})
	for _, e1 := range components {
		foundmatch := false
		for j, e2 := range other_components {
			_, taken := matched[j]
			if taken {
				continue
			}
			res := e1.IsEqual(e2, es)
			switch res {
			case "EQUAL_FALSE":
			case "EQUAL_TRUE":
				matched[j] = struct{}{}
				foundmatch = true
			case "EQUAL_UNK":
			}
			if foundmatch {
				break
			}
		}
		if !foundmatch {
			return "EQUAL_UNK"
		}
	}
	return "EQUAL_TRUE"
}

func CommutativeIsMatchQ(components []Ex, lhs_components []Ex, es *EvalState) bool {
	es.log.Infof("Entering CommutativeIsMatchQ")
	es.log.Infof("components: %s", ExArrayToString(components))
	es.log.Infof("lhs_components: %s", ExArrayToString(lhs_components))
	es.log.Debugf("Start of CommutativeIsMatchQ. Context:\n%v\n", es.ToString())
	if len(components) != len(lhs_components) {
		es.log.Debugf("len(components) != len(lhs_components). CommutativeMatchQ failed")
		return false
	}

	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(lhs_components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(lhs_components))

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		for i := range components {
			//es.log.Debugf("%s %s\n", components[i].ToString(), lhs_components[perm[pi]].ToString())
			if components[i].IsMatchQ(lhs_components[perm[pi]], es) {
				used[pi] = i
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					for tdi, todelete := range used {
						components = append(components[:todelete-tdi], components[todelete-tdi+1:]...)
					}
					es.log.Debugf("CommutativeIsMatchQ succeeded. Context: %s", es.ToString())
					return true
				}
			}
		}
	}
	es.log.Debugf("CommutativeIsMatchQ failed. Context: %s", es.ToString())
	return false
}

func FunctionIsEqual(components []Ex, other_components []Ex, es *EvalState) string {
	if len(components) != len(other_components) {
		return "EQUAL_FALSE"
	}
	for i := range components {
		res := components[i].IsEqual(other_components[i], es)
		switch res {
		case "EQUAL_FALSE":
			return "EQUAL_UNK"
		case "EQUAL_TRUE":
		case "EQUAL_UNK":
			return "EQUAL_UNK"
		}
	}
	return "EQUAL_TRUE"
}

func FunctionIsSameQ(components []Ex, other_components []Ex, es *EvalState) bool {
	if len(components) != len(other_components) {
		return false
	}
	for i := range components {
		res := components[i].IsSameQ(other_components[i], es)
		if !res {
			return false
		}
	}
	return true
}

func IterableReplace(components *[]Ex, r *Rule, es *EvalState) {
	for i := range *components {
		if (*components)[i].IsMatchQ(r.Lhs, es) {
			(*components)[i] = r.Rhs.DeepCopy()
		}
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

func CommutativeReplace(components *[]Ex, lhs_components []Ex, rhs Ex, es *EvalState) {
	es.log.Infof("Entering CommutativeReplace")
	es.log.Infof("components: %s", ExArrayToString(*components))
	es.log.Infof("lhs_components: %s", ExArrayToString(lhs_components))
	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(lhs_components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(lhs_components))

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		es.log.Debugf("Before snapshot. Context:\n%v\n", es.ToString())
		oldVars := es.GetDefinedSnapshot()
		for i := range *components {
			//es.log.Debugf("%s %s\n", (*components)[i].ToString(), lhs_components[perm[pi]].ToString())
			if (*components)[i].IsMatchQ(lhs_components[perm[pi]], es) {
				used[pi] = i
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					es.log.Debugf("About to delete components matching lhs.")
					es.log.Debugf("components before: %s", ExArrayToString(*components))
					for tdi, todelete := range used {
						*components = append((*components)[:todelete-tdi], (*components)[todelete-tdi+1:]...)
					}
					es.log.Debugf("components after: %s", ExArrayToString(*components))
					es.log.Debugf("Appending %s\n", rhs.ToString())
					es.log.Debugf("Context:\n%v\n", es.ToString())
					*components = append(*components, []Ex{rhs.DeepCopy()}...)
					es.log.Debugf("components after append: %s", ExArrayToString(*components))
					return
				}
			}
			es.log.Debugf("Done checking. Context:\n%v\n", es.ToString())
		}
		es.ClearPD()
		es.defined = oldVars
		es.log.Debugf("After clear. Context:\n%v\n", es.ToString())
	}
}
