package cas

import "bytes"

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
			a.addends[i] = &Flt{0}
		}
	}

	// Accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range a.addends {
		f, ok := e.(*Flt)
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
		f, ok := a.addends[i].(*Flt)
		if ok && f.Val == 0 {
			a.addends[i] = a.addends[len(a.addends)-1]
			a.addends[len(a.addends)-1] = nil
			a.addends = a.addends[:len(a.addends)-1]
		}
	}

	// If one expression remains, replace this Add with the expression
	if len(a.addends) == 1 {
		return a.addends[0]
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
