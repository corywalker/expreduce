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
	return f
}

type Add struct {
	addends []Ex
}

func (a Add) Eval() Ex {
	return a
}

func main() {
	var f Float = Float{5.5}
	fmt.Println(f)
	f = f.Eval().(Float)
	fmt.Println(f)
	var a = Add{[]Ex{Float{1}, Float{2}}}
	fmt.Println(a)
	ae := a.Eval()
	fmt.Println(ae)
}
