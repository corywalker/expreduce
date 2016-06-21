//go:generate go tool yacc -p Calc -o interp.go interp.y
//go:generate golex -o tokenizer.go tokenizer.l

package cas

type EvalState struct {
	defined map[string]Ex
}

func NewEvalState() *EvalState {
	var es EvalState
	es.defined = make(map[string]Ex)
	return &es
}

// Ex stands for Expression. Most structs should implement this
type Ex interface {
	Eval(es *EvalState) Ex
	ToString() string
	IsEqual(b Ex, es *EvalState) string
	//DeepCopy() *Ex
}

// Some utility functions that span multiple files

func CommutativeIsEqual(components []Ex, other_components []Ex, es *EvalState) string {
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
				return "EQUAL_UNK"
			}
			if foundmatch {
				break
			}
		}
		if !foundmatch {
			return "EQUAL_FALSE"
		}
	}
	return "EQUAL_TRUE"
}
