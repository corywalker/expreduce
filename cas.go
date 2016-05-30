package cas

import "fmt"
import "reflect"
import "bytes"

type Ex interface {
	Eval()
	ToString() string
}

type Float struct {
	Val float64
}

func (f *Float) Eval() {
	//f.Val += 1
	//return f
}

func (f *Float) ToString() string {
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
		fmt.Println(reflect.TypeOf(e))
		fmt.Println(reflect.TypeOf(a.addends))
		f, ok := e.(*Float)
		if ok {
			fmt.Println(f.Val)
			if lastf != nil {
				f.Val += lastf.Val;
				//a.addends[i] = f
				lastf.Val = 0
			}
			fmt.Println(f.Val)
			lastf = f
		}
	}
}

func (a Add) ToString() string {
	var buffer bytes.Buffer
	//var strList []string
	buffer.WriteString("(")
	for i, e := range a.addends {
		buffer.WriteString(e.ToString())
		if i != len(a.addends)-1 {
			buffer.WriteString(" + ")
		}
	}
	buffer.WriteString(")")
	return buffer.String()
	//return strings.Join(strList, " + ")
	//return fmt.Sprintf("{k}")
}
