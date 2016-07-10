package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
)

func Test(t *testing.T) {

	fmt.Println("Testing main CAS system")

	es := NewEvalState()

	// Test basic float functionality
	var f *Flt = &Flt{big.NewFloat(5.5)}
	assert.Equal(t, "5.5", f.ToString())
	f.Eval(es)
	assert.Equal(t, "5.5", f.ToString())

	// Test nested addition functionality
	var a = &Plus{[]Ex{
		&Plus{[]Ex{
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
		}},
		&Flt{big.NewFloat(2)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, "((80. + 3.) + 2. + 2.5)", a.ToString())
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test equality checking
	assert.Equal(t, "EQUAL_TRUE", (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(99)}, es))
	assert.Equal(t, "EQUAL_FALSE", (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(98)}, es))
	assert.Equal(t, "EQUAL_TRUE", (&Symbol{"x"}).IsEqual(&Symbol{"x"}, es))
	assert.Equal(t, "EQUAL_UNK", (&Symbol{"x"}).IsEqual(&Symbol{"X"}, es))
	assert.Equal(t, "EQUAL_UNK", (&Symbol{"x"}).IsEqual(&Symbol{"y"}, es))
	var t1 = &Plus{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Flt{big.NewFloat(5)},
	}}
	var t2 = &Plus{[]Ex{
		&Flt{big.NewFloat(5)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t1.IsEqual(t2, es))
	var b = &Plus{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Plus{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2)},
	}}
	var c = &Times{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Plus{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2)},
	}}
	var e = &Plus{[]Ex{
		&Flt{big.NewFloat(2.5)},
		&Plus{[]Ex{
			&Flt{big.NewFloat(3)},
			&Flt{big.NewFloat(80)},
		}},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(b, es))
	assert.Equal(t, "EQUAL_FALSE", a.IsEqual(c, es))
	assert.Equal(t, "EQUAL_FALSE", b.IsEqual(c, es))
	//assert.Equal(t, "EQUAL_FALSE", a.Eval(es).IsEqual(d.Eval(es), es))
	CasAssertSame(t, es, "False", "2.5 + (3. + 80.) + 2.5 == (80. + 3.) + 2. + 2.5")
	assert.Equal(t, "EQUAL_FALSE", a.IsEqual(e, es))
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, es))
	var t3 = &Plus{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	var t4 = &Plus{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t3.IsEqual(t4, es))
	t3 = &Plus{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	t4 = &Plus{[]Ex{
		&Symbol{"y"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_UNK", t3.IsEqual(t4, es))
	var t5 = &Times{[]Ex{
		&Flt{big.NewFloat(1)},
		&Symbol{"x"},
	}}
	var t6 = &Times{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t5.IsEqual(t6, es))

	// Test evaluation
	a.Eval(es)
	assert.Equal(t, "(87.5)", a.ToString())
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test basic Symbol functionality
	var v *Symbol = &Symbol{"x"}
	assert.Equal(t, "x", v.ToString())
	v.Eval(es)
	assert.Equal(t, "x", v.ToString())

	// Test nested addition functionality
	var withVar = &Plus{[]Ex{
		&Plus{[]Ex{
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
	withVar = &Plus{[]Ex{
		&Plus{[]Ex{
			&Symbol{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Times{[]Ex{
			&Symbol{"x"},
			&Flt{big.NewFloat(2)},
			&Flt{big.NewFloat(2)},
		}},
		&Times{[]Ex{
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

	assert.Equal(t, "(a + b + c + d + e + f)", EasyRun("a + b + c +d +e +f", es))
	assert.Equal(t, "(a * b * c * d * e * f)", EasyRun("a * b * c *d *e *f", es))

	CasAssertSame(t, es, "2", "test = 2")
	_, containsTest := es.defined["test"]
	assert.True(t, containsTest)
	es.ClearAll()
	_, containsTest = es.defined["test"]
	assert.False(t, containsTest)
}
