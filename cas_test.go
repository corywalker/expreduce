package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func Test(t *testing.T) {

	// Test basic float functionality
	var f *Flt = &Flt{big.NewFloat(5.5)}
	assert.Equal(t, f.ToString(), "5.5")
	f.Eval()
	assert.Equal(t, f.ToString(), "5.5")

	// Test nested addition functionality
	var a = &Add{[]Ex{
		&Add{[]Ex{
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
		}},
		&Flt{big.NewFloat(2)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, a.ToString(), "((80 + 3) + 2 + 2.5)")
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test equality checking
	assert.Equal(t, (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(99)}), "EQUAL_TRUE")
	assert.Equal(t, (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(98)}), "EQUAL_FALSE")
	assert.Equal(t, (&Variable{"x"}).IsEqual(&Variable{"x"}), "EQUAL_TRUE")
	assert.Equal(t, (&Variable{"x"}).IsEqual(&Variable{"X"}), "EQUAL_FALSE")
	assert.Equal(t, (&Variable{"x"}).IsEqual(&Variable{"y"}), "EQUAL_FALSE")
	var t1 = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Flt{big.NewFloat(5)},
	}}
	var t2 = &Add{[]Ex{
		&Flt{big.NewFloat(5)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, t1.IsEqual(t2), "EQUAL_TRUE")
	var b = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Add{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2)},
	}}
	var c = &Mul{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Add{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2)},
	}}
	var d = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Add{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2)},
		&Variable{"x"},
	}}
	var e = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Add{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, a.IsEqual(b), "EQUAL_TRUE")
	assert.Equal(t, a.IsEqual(c), "EQUAL_FALSE")
	assert.Equal(t, b.IsEqual(c), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(d), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(e), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(a), "EQUAL_TRUE")
	var t3 = &Add{[]Ex{
		&Flt{big.NewFloat(1)},
		&Variable{"x"},
	}}
	var t4 = &Add{[]Ex{
		&Variable{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t3.IsEqual(t4))
	t3 = &Add{[]Ex{
		&Flt{big.NewFloat(1)},
		&Variable{"x"},
	}}
	t4 = &Add{[]Ex{
		&Variable{"y"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_FALSE", t3.IsEqual(t4))
	var t5 = &Mul{[]Ex{
		&Flt{big.NewFloat(1)},
		&Variable{"x"},
	}}
	var t6 = &Mul{[]Ex{
		&Variable{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t5.IsEqual(t6))
	var t7 = &Mul{[]Ex{
		&Flt{big.NewFloat(1)},
		&Variable{"x"},
	}}
	var t8 = &Variable{"x"}
	assert.Equal(t, "EQUAL_TRUE", t7.IsEqual(t8))

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
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Variable{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Variable{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	fmt.Println(withVar.ToString())
	withVar.Eval()
	fmt.Println(withVar.ToString())

	// Test nested addition and multiplication functionality
	withVar = &Add{[]Ex{
		&Add{[]Ex{
			&Variable{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Variable{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Mul{[]Ex{
			&Variable{"x"},
			&Flt{big.NewFloat(2)},
			&Flt{big.NewFloat(2)},
		}},
		&Mul{[]Ex{
			&Flt{big.NewFloat(0)},
			&Flt{big.NewFloat(3)},
			&Variable{"x"},
		}},
		&Variable{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	fmt.Println(withVar.ToString())
	withVar.Eval()
	fmt.Println(withVar.ToString())
}
