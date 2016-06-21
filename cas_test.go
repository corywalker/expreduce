package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func Test(t *testing.T) {

	fmt.Println("Testing main CAS system")

	es := NewEvalState()

	// Test basic float functionality
	var f *Flt = &Flt{big.NewFloat(5.5)}
	assert.Equal(t, f.ToString(), "5.5")
	f.Eval(es)
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
	assert.Equal(t, (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(99)}, es), "EQUAL_TRUE")
	assert.Equal(t, (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(98)}, es), "EQUAL_FALSE")
	assert.Equal(t, (&Symbol{"x"}).IsEqual(&Symbol{"x"}, es), "EQUAL_TRUE")
	assert.Equal(t, (&Symbol{"x"}).IsEqual(&Symbol{"X"}, es), "EQUAL_FALSE")
	assert.Equal(t, (&Symbol{"x"}).IsEqual(&Symbol{"y"}, es), "EQUAL_FALSE")
	var t1 = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Flt{big.NewFloat(5)},
	}}
	var t2 = &Add{[]Ex{
		&Flt{big.NewFloat(5)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, t1.IsEqual(t2, es), "EQUAL_TRUE")
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
		&Symbol{"x"},
	}}
	var e = &Add{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Add{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, a.IsEqual(b, es), "EQUAL_TRUE")
	assert.Equal(t, a.IsEqual(c, es), "EQUAL_FALSE")
	assert.Equal(t, b.IsEqual(c, es), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(d, es), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(e, es), "EQUAL_FALSE")
	assert.Equal(t, a.IsEqual(a, es), "EQUAL_TRUE")
	var t3 = &Add{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	var t4 = &Add{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t3.IsEqual(t4, es))
	t3 = &Add{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	t4 = &Add{[]Ex{
		&Symbol{"y"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_FALSE", t3.IsEqual(t4, es))
	var t5 = &Mul{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	var t6 = &Mul{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t5.IsEqual(t6, es))
	var t7 = &Mul{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	var t8 = &Symbol{"x"}
	assert.Equal(t, "EQUAL_TRUE", t7.IsEqual(t8, es))

	// Test evaluation
	a.Eval(es)
	assert.Equal(t, a.ToString(), "(87.5)")
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test basic Symbol functionality
	var v *Symbol = &Symbol{"x"}
	assert.Equal(t, v.ToString(), "x")
	v.Eval(es)
	assert.Equal(t, v.ToString(), "x")

	// Test nested addition functionality
	var withVar = &Add{[]Ex{
		&Add{[]Ex{
			&Symbol{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Symbol{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	fmt.Println(withVar.ToString())
	withVar.Eval(es)
	fmt.Println(withVar.ToString())

	// Test nested addition and multiplication functionality
	withVar = &Add{[]Ex{
		&Add{[]Ex{
			&Symbol{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Mul{[]Ex{
			&Symbol{"x"},
			&Flt{big.NewFloat(2)},
			&Flt{big.NewFloat(2)},
		}},
		&Mul{[]Ex{
			&Flt{big.NewFloat(0)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Symbol{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	fmt.Println(withVar.ToString())
	withVar.Eval(es)
	fmt.Println(withVar.ToString())
}
