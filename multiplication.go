package cas

import "bytes"
import "math/big"

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
			m.multiplicands[i] = &Flt{big.NewFloat(1)}
		}
	}

	// If there is a zero in the expression, return zero
	for _, e := range m.multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return &Flt{big.NewFloat(0)}
			}
		}
	}

	// Geometrically accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range m.multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if lastf != nil {
				f.Val.Mul(f.Val, lastf.Val)
				lastf.Val = big.NewFloat(1)
			}
			lastf = f
		}
	}

	// Remove one Floats
	for i := len(m.multiplicands)-1; i >= 0; i-- {
		f, ok := m.multiplicands[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(1)) == 0 {
			m.multiplicands[i] = m.multiplicands[len(m.multiplicands)-1]
			m.multiplicands[len(m.multiplicands)-1] = nil
			m.multiplicands = m.multiplicands[:len(m.multiplicands)-1]
		}
	}

	// If one expression remains, replace this Mul with the expression
	if len(m.multiplicands) == 1 {
		return m.multiplicands[0]
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
