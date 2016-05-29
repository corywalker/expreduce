package cas

//import "fmt"

type Ex interface {
	Eval() Ex
}

type Float struct {
	val float64
}

func (f Float) Eval() Ex {
	f.val = 99
	return f
}

type Add struct {
	addends []Ex
}

func (a Add) Eval() Ex {
	for i := range a.addends {
		a.addends[i] = a.addends[i].Eval()
	}
	return a
}
