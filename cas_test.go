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
	var a = &Expression{[]Ex{
		&Symbol{"Plus"},
		&Expression{[]Ex{
			&Symbol{"Plus"},
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
	var t1 = &Expression{[]Ex{
		&Symbol{"Plus"},
		&Flt{big.NewFloat(2.5)},
		&Flt{big.NewFloat(5)},
	}}
	var t2 = &Expression{[]Ex{
		&Symbol{"Plus"},
		&Flt{big.NewFloat(5)},
		&Flt{big.NewFloat(2.5)},
	}}
	assert.Equal(t, "EQUAL_TRUE", t1.IsEqual(t2, es))
	CasAssertSame(t, es, "False", "2.5 + (3. + 80.) + 2.5 == (80. + 3.) + 2. + 2.5")

	// Test evaluation
	newa := a.Eval(es)
	assert.Equal(t, "87.5", newa.ToString())
	//fmt.Println(a)
	//fmt.Println(a.ToString())

	// Test basic Symbol functionality
	var v *Symbol = &Symbol{"x"}
	assert.Equal(t, "x", v.ToString())
	v.Eval(es)
	assert.Equal(t, "x", v.ToString())

	// Test nested addition functionality
	var withVar = &Expression{[]Ex{
		&Symbol{"Plus"},
		&Expression{[]Ex{
			&Symbol{"Plus"},
			&Symbol{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Symbol{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	withVar.Eval(es)

	// Test nested addition and multiplication functionality
	withVar = &Expression{[]Ex{
		&Symbol{"Plus"},
		&Expression{[]Ex{
			&Symbol{"Plus"},
			&Symbol{"x"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Flt{big.NewFloat(2)},
		&Expression{[]Ex{
			&Symbol{"Times"},
			&Symbol{"x"},
			&Flt{big.NewFloat(2)},
			&Flt{big.NewFloat(2)},
		}},
		&Expression{[]Ex{
			&Symbol{"Times"},
			&Flt{big.NewFloat(0)},
			&Flt{big.NewFloat(3)},
			&Symbol{"x"},
		}},
		&Symbol{"x"},
		&Flt{big.NewFloat(2.5)},
	}}
	//fmt.Println(withVar.ToString())
	withVar.Eval(es)
	//fmt.Println(withVar.ToString())

	assert.Equal(t, "(a + b + c + d + e + f)", EasyRun("a + b + c +d +e +f", es))
	assert.Equal(t, "(a * b * c * d * e * f)", EasyRun("a * b * c *d *e *f", es))

	CasAssertSame(t, es, "2", "test = 2")
	_, containsTest := es.defined["test"]
	assert.True(t, containsTest)
	es.ClearAll()
	_, containsTest = es.defined["test"]
	assert.False(t, containsTest)
}
