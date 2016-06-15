package cas

import "fmt"
import "bytes"

// Ex stands for Expression. Most structs should implement this
type Ex interface {
	Eval() Ex
	ToString() string
	IsEqual(b Ex) string
}

/*
func isEqual(a Ex, b Ex) string {
	switch v := a.(type) {
	case Float:
		// here v has type T
	case Add:
		// here v has type S
	case Mul:
		// here v has type S
	default:
		return "EQUAL_UNK"
	}
	return false
} */


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

// Floating point numbers represented by float64
type Float struct {
	Val float64
}

func (f *Float) Eval() Ex {
	return f
}

func (f *Float) ToString() string {
	return fmt.Sprintf("%g", f.Val)
}

func (this *Float) IsEqual(other Ex) string {
	otherConv, ok := other.(*Float)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Val != otherConv.Val {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
}

// A sequence of Expressions to be added together
type Add struct {
	addends []Ex
}

func (a *Add) Eval() Ex {
	// Start by evaluating each addend
	for i := range a.addends {
		a.addends[i] = a.addends[i].Eval()
	}

	// If any of the addends are also Adds, merge them with a and remove them
	// We can easily remove an item by replacing it with a zero float.
	for i, e := range a.addends {
		subadd, isadd := e.(*Add)
		if isadd {
			a.addends = append(a.addends, subadd.addends...)
			a.addends[i] = &Float{0}
		}
	}

	// Accumulate floating point values towards the end of the expression
	var lastf *Float = nil
	for _, e := range a.addends {
		f, ok := e.(*Float)
		if ok {
			if lastf != nil {
				f.Val += lastf.Val;
				lastf.Val = 0
			}
			lastf = f
		}
	}

	// Remove zero Floats
	for i := len(a.addends)-1; i >= 0; i-- {
		f, ok := a.addends[i].(*Float)
		if ok && f.Val == 0 {
			a.addends[i] = a.addends[len(a.addends)-1]
			a.addends[len(a.addends)-1] = nil
			a.addends = a.addends[:len(a.addends)-1]
		}
	}

	// If one float remains, replace this Add with the Float
	if len(a.addends) == 1 {
		_, isfloat := a.addends[0].(*Float)
		if isfloat {
			return a.addends[0]
		}
	}

	return a
}

func (a *Add) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range a.addends {
		buffer.WriteString(e.ToString())
		if i != len(a.addends)-1 {
			buffer.WriteString(" + ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Add) IsEqual(otherEx Ex) string {
	thisEx := this.Eval()
	otherEx = otherEx.Eval()
	this, ok := thisEx.(*Add)
	if !ok {
		return thisEx.IsEqual(otherEx)
	}
	other, ok := otherEx.(*Add)
	if !ok {
		return "EQUAL_FALSE"
	}
	return CommutativeIsEqual(this.addends, other.addends)
}

// A sequence of Expressions to be multiplied together
type Mul struct {
	multiplicands []Ex
}

func (m *Mul) Eval() Ex {
	// Start by evaluating each multiplicand
	for i := range m.multiplicands {
		m.multiplicands[i] = m.multiplicands[i].Eval()
	}

	// If any of the multiplicands are also Muls, merge them with m and remove them
	// We can easily remove an item by replacing it with a one float.
	for i, e := range m.multiplicands {
		submul, ismul := e.(*Mul)
		if ismul {
			m.multiplicands = append(m.multiplicands, submul.multiplicands...)
			m.multiplicands[i] = &Float{1}
		}
	}

	// If there is a zero in the expression, return zero
	for _, e := range m.multiplicands {
		f, ok := e.(*Float)
		if ok {
			if f.Val == 0 {
				return &Float{0}
			}
		}
	}

	// Geometrically accumulate floating point values towards the end of the expression
	var lastf *Float = nil
	for _, e := range m.multiplicands {
		f, ok := e.(*Float)
		if ok {
			if lastf != nil {
				f.Val *= lastf.Val;
				lastf.Val = 1
			}
			lastf = f
		}
	}

	// Remove one Floats
	for i := len(m.multiplicands)-1; i >= 0; i-- {
		f, ok := m.multiplicands[i].(*Float)
		if ok && f.Val == 1 {
			m.multiplicands[i] = m.multiplicands[len(m.multiplicands)-1]
			m.multiplicands[len(m.multiplicands)-1] = nil
			m.multiplicands = m.multiplicands[:len(m.multiplicands)-1]
		}
	}

	// If one float remains, replace this Mul with the Float
	if len(m.multiplicands) == 1 {
		_, isfloat := m.multiplicands[0].(*Float)
		if isfloat {
			return m.multiplicands[0]
		}
	}

	return m
}

func (m *Mul) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range m.multiplicands {
		buffer.WriteString(e.ToString())
		if i != len(m.multiplicands)-1 {
			buffer.WriteString(" * ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Mul) IsEqual(otherEx Ex) string {
	thisEx := this.Eval()
	otherEx = otherEx.Eval()
	this, ok := thisEx.(*Mul)
	if !ok {
		return thisEx.IsEqual(otherEx)
	}
	other, ok := otherEx.(*Mul)
	if !ok {
		return "EQUAL_FALSE"
	}
	return CommutativeIsEqual(this.multiplicands, other.multiplicands)
}

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
