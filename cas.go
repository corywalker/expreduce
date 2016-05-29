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
	f.val = 6
	return f
}

func main() {
	fmt.Println("Hi")
	//var x Ex
	//x := Float{5.5}
	var f Float = Float{5.5}
	fmt.Println(f)
	f = f.Eval().(Float)
	fmt.Println(f)
}
