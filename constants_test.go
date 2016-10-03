package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
)

func TestConstants(t *testing.T) {

	fmt.Println("Testing constants")

	es := NewEvalState()

	var a Ex = &Expression{[]Ex{
		&Symbol{"Times"},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(-1)},
		&Symbol{"x"},
	}}
	var res Ex = a.Eval(es)
	assert.Equal(t, "(-1.0000000000000003e+360 * x)", res.ToString())

	a = &Symbol{"True"}
	assert.Equal(t, "True", a.ToString())
	var b Ex = &Symbol{"False"}
	assert.Equal(t, "False", b.ToString())
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, es))
	assert.Equal(t, "EQUAL_TRUE", b.IsEqual(b, es))
	assert.Equal(t, "EQUAL_FALSE", a.IsEqual(b, es))
	assert.Equal(t, "EQUAL_FALSE", b.IsEqual(a, es))
	//fmt.Println(a.ToString())

	a = &Error{"First error"}
	assert.Equal(t, "First error", a.ToString())
	b = &Error{"Second error"}
	assert.Equal(t, "Second error", b.ToString())
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, es))
	assert.Equal(t, "EQUAL_TRUE", b.IsEqual(b, es))
	assert.Equal(t, "EQUAL_FALSE", a.IsEqual(b, es))
	assert.Equal(t, "EQUAL_FALSE", b.IsEqual(a, es))
}
