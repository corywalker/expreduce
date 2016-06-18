//go:generate go tool yacc -p Calc -o calc.go calc.y

package cas

// Ex stands for Expression. Most structs should implement this
type Ex interface {
	Eval() Ex
	ToString() string
	IsEqual(b Ex) string
}

// Some utility functions that span multiple files

func CommutativeIsEqual(components []Ex, other_components []Ex) string {
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
			res := e1.IsEqual(e2)
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
