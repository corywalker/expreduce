package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)


func Test(t *testing.T) {

	// Test basic float functionality
	var f *Float = &Float{5.5}
	assert.Equal(t, f.ToString(), "5.5")
	f.Eval()
	assert.Equal(t, f.ToString(), "5.5")

	// Test nested addition functionality
	var a = &Add{[]Ex{
		&Add{[]Ex{
			&Float{80},
			&Float{3},
		}},
		&Float{2},
		&Float{2.5},
	}}
	assert.Equal(t, a.ToString(), "((80 + 3) + 2 + 2.5)")
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test evaluation
	a.Eval()
	assert.Equal(t, a.ToString(), "(87.5)")
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test basic Variable functionality
	var v *Variable = &Variable{"x"}
	assert.Equal(t, v.ToString(), "x")
	v.Eval()
	assert.Equal(t, v.ToString(), "x")

	// Test nested addition functionality
	var withVar = &Add{[]Ex{
		&Add{[]Ex{
			&Variable{"x"},
			&Float{80},
			&Float{3},
			&Variable{"x"},
		}},
		&Float{2},
		&Variable{"x"},
		&Float{2.5},
	}}
	fmt.Println(withVar.ToString())
	withVar.Eval()
	fmt.Println(withVar.ToString())
}
