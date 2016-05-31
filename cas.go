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

func (f *Float) Eval() {
}

func (f *Float) ToString() string {
	return fmt.Sprintf("%f", f.Val)
}

type Add struct {
	addends []Ex
}

func (a *Add) Eval() {
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

	fmt.Println("Evaluating")
	fmt.Println(len(a.addends))
	for i := len(a.addends)-1; i >= 0; i-- {
		f, ok := a.addends[i].(*Float)
		if ok && f.Val == 0 {
			//a.addends = append(a.addends[:i], a.addends[i+1:]...)
			//copy(a.addends[i:], a.addends[i+1:])
			//a.addends[len(a.addends)-1] = nil // or the zero value of T
			//a.addends = a.addends[:len(a.addends)-1]
			a.addends[i] = a.addends[len(a.addends)-1]
			a.addends[len(a.addends)-1] = nil
			a.addends = a.addends[:len(a.addends)-1]
		}
	}
	fmt.Println(len(a.addends))
}

func (a *Add) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	fmt.Println("Printing")
	fmt.Println(len(a.addends))
	for i, e := range a.addends {
		buffer.WriteString(e.ToString())
		if i != len(a.addends)-1 {
			buffer.WriteString(" + ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
}
