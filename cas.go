//go:generate go tool yacc -p Calc -o interp.go interp.y
//go:generate golex -o tokenizer.go tokenizer.l

package cas

import (
	"bytes"
	"github.com/op/go-logging"
	"os"
	"sort"
	"strings"
)

var format = logging.MustStringFormatter(
	`%{color}%{time:15:04:05.000} %{shortfunc} ▶ %{level:.4s} %{id:03x}%{color:reset} %{message}`,
)

type EvalState struct {
	defined        map[string]Ex
	patternDefined map[string]Ex
	log            *logging.Logger
	leveled        logging.LeveledBackend
	logDepth       int
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
	es.logDepth = -1

	return &es
}

func (this *EvalState) DebugOn() {
	this.leveled.SetLevel(logging.DEBUG, "")
}

func (this *EvalState) DebugOff() {
	this.leveled.SetLevel(logging.ERROR, "")
}

func (this *EvalState) Pre() string {
	toReturn := ""
	for i := 0; i < this.logDepth; i++ {
		toReturn += " "
	}
	return toReturn
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
	buffer.WriteString("{")
	for k, v := range this.defined {
		buffer.WriteString(k)
		buffer.WriteString(": ")
		buffer.WriteString(v.ToString())
		buffer.WriteString(", ")
	}
	for k, v := range this.defined {
		buffer.WriteString(k)
		buffer.WriteString("_: ")
		buffer.WriteString(v.ToString())
		buffer.WriteString(", ")
	}
	if strings.HasSuffix(buffer.String(), ", ") {
		buffer.Truncate(buffer.Len() - 2)
	}
	buffer.WriteString("}")
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
	es.logDepth++
	es.log.Infof(es.Pre()+"Entering CommutativeIsEqual(components: %s, other_components: %s, es: %s)", ExArrayToString(components), ExArrayToString(other_components), es.ToString())
	if len(components) != len(other_components) {
		es.logDepth--
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
			es.logDepth--
			return "EQUAL_UNK"
		}
	}
	es.logDepth--
	return "EQUAL_TRUE"
}

func CommutativeIsMatchQ(components []Ex, lhs_components []Ex, es *EvalState) bool {
	es.logDepth++
	es.log.Infof(es.Pre()+"Entering CommutativeIsMatchQ(components: %s, lhs_components: %s, es: %s)", ExArrayToString(components), ExArrayToString(lhs_components), es.ToString())
	if len(components) != len(lhs_components) {
		es.log.Debugf(es.Pre() + "len(components) != len(lhs_components). CommutativeMatchQ failed")
		es.logDepth--
		return false
	}

	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(lhs_components))
	es.log.Debugf(es.Pre()+"Permutations to try: %v\n", perms)

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		for i := range perm {
			//es.log.Debugf(es.Pre()+"%s %s\n", components[i].ToString(), lhs_components[perm[pi]].ToString())
			if components[perm[i]].DeepCopy().IsMatchQ(lhs_components[i], es) {
				used[pi] = perm[i]
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					for tdi, todelete := range used {
						components = append(components[:todelete-tdi], components[todelete-tdi+1:]...)
					}
					es.log.Debugf(es.Pre()+"CommutativeIsMatchQ succeeded. Context: %s", es.ToString())
					es.logDepth--
					return true
				}
			}
		}
	}
	es.log.Debugf(es.Pre()+"CommutativeIsMatchQ failed. Context: %s", es.ToString())
	es.logDepth--
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
	es.logDepth++
	for i := range *components {
		es.log.Debugf(es.Pre()+"Attempting (%s).IsMatchQ(%s, %s)", (*components)[i].ToString(), r.Lhs.ToString(), es.ToString())
		oldVars := es.GetDefinedSnapshot()
		if (*components)[i].IsMatchQ(r.Lhs, es) {
			(*components)[i] = r.Rhs.DeepCopy()
			es.log.Debugf(es.Pre()+"IsMatchQ succeeded, new components: %s", ExArrayToString(*components))
		}
		es.ClearPD()
		es.defined = oldVars
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
	es.logDepth++
	es.log.Infof(es.Pre()+"Entering CommutativeReplace(components: *%s, lhs_components: %s, es: %s)", ExArrayToString(*components), ExArrayToString(lhs_components), es.ToString())
	// Each permutation is a potential order of the Rule's LHS in which matches
	// may occur in components.
	toPermute := make([]int, len(*components))
	for i := range toPermute {
		toPermute[i] = i
	}
	perms := permutations(toPermute, len(lhs_components))
	es.log.Debugf(es.Pre()+"Permutations to try: %v\n", perms)

	for _, perm := range perms {
		used := make([]int, len(perm))
		pi := 0
		es.log.Debugf(es.Pre()+"Before snapshot. Context: %v\n", es.ToString())
		oldVars := es.GetDefinedSnapshot()
		for i := range perm {
			//es.log.Debugf(es.Pre()+"%s %s\n", (*components)[perm[i]].ToString(), lhs_components[i].ToString())
			if (*components)[perm[i]].DeepCopy().IsMatchQ(lhs_components[i], es) {
				used[pi] = perm[i]
				pi = pi + 1

				if pi == len(perm) {
					sort.Ints(used)
					es.log.Debugf(es.Pre() + "About to delete components matching lhs.")
					es.log.Debugf(es.Pre()+"components before: %s", ExArrayToString(*components))
					for tdi, todelete := range used {
						*components = append((*components)[:todelete-tdi], (*components)[todelete-tdi+1:]...)
					}
					es.log.Debugf(es.Pre()+"components after: %s", ExArrayToString(*components))
					es.log.Debugf(es.Pre()+"Appending %s\n", rhs.ToString())
					es.log.Debugf(es.Pre()+"Context: %v\n", es.ToString())
					*components = append(*components, []Ex{rhs.DeepCopy().Eval(es)}...)
					es.log.Debugf(es.Pre()+"components after append: %s", ExArrayToString(*components))
					es.ClearPD()
					es.defined = oldVars
					es.log.Debugf(es.Pre()+"After clear. Context: %v\n", es.ToString())
					es.logDepth--
					return
				}
			}
			es.log.Debugf(es.Pre()+"Done checking. Context: %v\n", es.ToString())
		}
		es.ClearPD()
		es.defined = oldVars
		es.log.Debugf(es.Pre()+"After clear. Context: %v\n", es.ToString())
	}
	es.logDepth--
}
