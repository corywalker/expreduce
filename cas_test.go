package cas

import "testing"
import "fmt"

func Test(t *testing.T) {
	var f *Float = &Float{5.5}
	fmt.Println(f)
	f.Eval()
	fmt.Println(f)
	var a = &Add{[]Ex{
		&Add{[]Ex{
			&Float{80},
			&Float{3},
		}},
		&Float{2},
	}}
	fmt.Println(a)
	fmt.Println(a.ToString())
	a.Eval()
	fmt.Println(a)
	fmt.Println(a.ToString())
}
