package cas

import "bytes"
import "math/big"

// A sequence of Expressions to be multiplied together
type Mul struct {
	Multiplicands []Ex
}

func (m *Mul) Eval(es *EvalState) Ex {
	// Start by evaluating each multiplicand
	for i := range m.Multiplicands {
		m.Multiplicands[i] = m.Multiplicands[i].Eval(es)
	}

	// If any of the multiplicands are also Muls, merge them with m and remove them
	// We can easily remove an item by replacing it with a one float.
	for i, e := range m.Multiplicands {
		submul, ismul := e.(*Mul)
		if ismul {
			m.Multiplicands = append(m.Multiplicands, submul.Multiplicands...)
			m.Multiplicands[i] = &Flt{big.NewFloat(1)}
		}
	}

	// If there is a zero in the expression, return zero
	for _, e := range m.Multiplicands {
		f, ok := e.(*Flt)
		if ok {
			if f.Val.Cmp(big.NewFloat(0)) == 0 {
				return &Flt{big.NewFloat(0)}
			}
		}
	}

	// Geometrically accumulate floating point values towards the end of the expression
	var lastf *Flt = nil
	for _, e := range m.Multiplicands {
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
	for i := len(m.Multiplicands)-1; i >= 0; i-- {
		f, ok := m.Multiplicands[i].(*Flt)
		if ok && f.Val.Cmp(big.NewFloat(1)) == 0 {
			m.Multiplicands[i] = m.Multiplicands[len(m.Multiplicands)-1]
			m.Multiplicands[len(m.Multiplicands)-1] = nil
			m.Multiplicands = m.Multiplicands[:len(m.Multiplicands)-1]
		}
	}

	// If one expression remains, replace this Mul with the expression
	if len(m.Multiplicands) == 1 {
		return m.Multiplicands[0]
	}

	return m
}

func (m *Mul) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i, e := range m.Multiplicands {
		buffer.WriteString(e.ToString())
		if i != len(m.Multiplicands)-1 {
			buffer.WriteString(" * ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Mul) IsEqual(otherEx Ex, es *EvalState) string {
	thisEx := this.Eval(es)
	otherEx = otherEx.Eval(es)
	this, ok := thisEx.(*Mul)
	if !ok {
		return thisEx.IsEqual(otherEx, es)
	}
	other, ok := otherEx.(*Mul)
	if !ok {
		return "EQUAL_FALSE"
	}
	return CommutativeIsEqual(this.Multiplicands, other.Multiplicands, es)
}
