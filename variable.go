package cas

import "fmt"

// Variables are defined by a string-based name
type Variable struct {
	Name string
}

func (v *Variable) Eval() Ex {
	return v
}

func (v *Variable) ToString() string {
	return fmt.Sprintf("%v", v.Name)
}

func (this *Variable) IsEqual(other Ex) string {
	otherConv, ok := other.(*Variable)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Name != otherConv.Name {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}
