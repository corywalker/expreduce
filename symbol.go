package cas

import "fmt"

// Symbols are defined by a string-based name
type Symbol struct {
	Name string
}

func (v *Symbol) Eval(es EvalState) Ex {
	return v
}

func (v *Symbol) ToString() string {
	return fmt.Sprintf("%v", v.Name)
}

func (this *Symbol) IsEqual(other Ex, es EvalState) string {
	otherConv, ok := other.(*Symbol)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Name != otherConv.Name {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}
