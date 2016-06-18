package cas

import "bytes"
import "math/big"

// A sequence of Expressions to be added together
type Add struct {
	Addends []Ex
}

func (a *Add) Eval() Ex {
	// Start by evaluating each addend
	for i := range a.Addends {
		a.Addends[i] = a.Addends[i].Eval()
	}

	// If any of the addends are also Adds, merge them with a and remove them
	// We can easily remove an item by replacing it with a zero float.
	for i, e := range a.Addends {
		subadd, isadd := e.(*Add)
		if isadd {
			a.Addends = append(a.Addends, subadd.Addends...)
			a.Addends[i] = &Flt{big.NewFloat(0)}
		}
	}

	// Accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range a.Addends {
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				f.Val.Add(f.Val, lastf.Val)
				lastf.Val = big.NewFloat(0)
			}
			lastf = f
		}
	}

	// Remove zero Floats
	for i := len(a.Addends)-1; i >= 0; i-- {
		f, ok := a.Addends[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(0)) == 0 {
			a.Addends[i] = a.Addends[len(a.Addends)-1]
			a.Addends[len(a.Addends)-1] = nil
			a.Addends = a.Addends[:len(a.Addends)-1]
		}
	}

	// If one expression remains, replace this Add with the expression
	if len(a.Addends) == 1 {
		return a.Addends[0]
	}

	return a
}

func (a *Add) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range a.Addends {
		buffer.WriteString(e.ToString())
		if i != len(a.Addends)-1 {
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
	return CommutativeIsEqual(this.Addends, other.Addends)
}
