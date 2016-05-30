package cas

//import "fmt"
//import "reflect"

type Ex interface {
	Eval()
}

type Float struct {
	Val float64
}

func (f *Float) Eval() {
	//f.Val += 1
	//return f
}

/*
type Add struct {
	addends []Ex
}

func (a Add) Eval() Ex {
	for i := range a.addends {
		a.addends[i] = a.addends[i].Eval()
	}

	var lastf *Float = nil
	for _, e := range a.addends {
		fmt.Println(reflect.TypeOf(e))
		fmt.Println(reflect.TypeOf(a.addends))
		f := e.(*Float)
		ok := true
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

	return a
}
*/
