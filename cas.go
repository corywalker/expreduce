package cas

import "fmt"
import "bytes"

type Ex interface {
	Eval()
	ToString() string
}

type Float struct {
	Val float64
}

func (f Float) Eval() {
}

func (f Float) ToString() string {
	return fmt.Sprintf("%f", f.Val)
}

type Add struct {
	addends []Ex
}

func (a Add) Eval() {
	for i := range a.addends {
		a.addends[i].Eval()
	}

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
}

func (a Add) ToString() string {
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
