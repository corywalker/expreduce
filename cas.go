package main

import (
	"fmt"
)

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

func main() {
	var f Float = Float{5.5}
	fmt.Println(f)
	f = f.Eval().(Float)
	fmt.Println(f)
	var a = Add{[]Ex{
		Add{[]Ex{
			Float{80},
			Float{3},
		}},
		Float{2},
	}}
	fmt.Println(a)
	ae := a.Eval()
	fmt.Println(ae)
}
