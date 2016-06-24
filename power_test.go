package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestPower(t *testing.T) {
	fmt.Println("Testing exponents")

	es := NewEvalState()

	var t9 = &Power{
		&Symbol{"x"},
		&Flt{big.NewFloat(2)},
	}
	var t10 = &Power{
		&Symbol{"x"},
		&Plus{[]Ex{&Flt{big.NewFloat(-1)}, &Flt{big.NewFloat(3)}}},
	}
	var t11 = &Power{
		&Symbol{"x"},
		&Flt{big.NewFloat(3)},
	}
	assert.Equal(t, "x^2.", t9.ToString())
	assert.Equal(t, "x^(-1. + 3.)", t10.ToString())
	assert.Equal(t, "x^3.", t11.ToString())
	assert.Equal(t, "EQUAL_TRUE", t9.IsEqual(t10, es))
	assert.Equal(t, "EQUAL_UNK", t9.IsEqual(t11, es))

	// Test raising expressions to the first power
	assert.Equal(t, "(x + 1)", EvalInterp("(x+1)^1", es).ToString())
	assert.Equal(t, "0", EvalInterp("0^1", es).ToString())
	assert.Equal(t, "0.", EvalInterp("0.^1", es).ToString())
	assert.Equal(t, "-5", EvalInterp("-5^1", es).ToString())
	assert.Equal(t, "-5.5", EvalInterp("-5.5^1", es).ToString())
	assert.Equal(t, "(x + 1)", EvalInterp("(x+1)^1.", es).ToString())
	assert.Equal(t, "0", EvalInterp("0^1.", es).ToString())
	assert.Equal(t, "0.", EvalInterp("0.^1.", es).ToString())
	assert.Equal(t, "-5", EvalInterp("(-5)^1.", es).ToString())
	assert.Equal(t, "-5.5", EvalInterp("-5.5^1.", es).ToString())

	// Test raising expressions to the zero power
	assert.Equal(t, "1", EvalInterp("(x+1)^0", es).ToString())
	assert.Equal(t, "Indeterminate", EvalInterp("0^0", es).ToString())
	assert.Equal(t, "Indeterminate", EvalInterp("0.^0", es).ToString())
	assert.Equal(t, "-1", EvalInterp("-5^0", es).ToString())
	assert.Equal(t, "1", EvalInterp("(-5)^0", es).ToString())
	assert.Equal(t, "1", EvalInterp("(-5.5)^0", es).ToString())
	assert.Equal(t, "1", EvalInterp("(x+1)^0.", es).ToString())
	assert.Equal(t, "Indeterminate", EvalInterp("0^0.", es).ToString())
	assert.Equal(t, "Indeterminate", EvalInterp("0.^0.", es).ToString())
	assert.Equal(t, "-1", EvalInterp("-5^0.", es).ToString())
	assert.Equal(t, "1", EvalInterp("(-5.5)^0.", es).ToString())
	assert.Equal(t, "-1", EvalInterp("-5^0", es).ToString())
	assert.Equal(t, "1", EvalInterp("99^0", es).ToString())

	assert.Equal(t, "125", EvalInterp("5^3", es).ToString())
	assert.Equal(t, "125^-1", EvalInterp("5^-3", es).ToString())
	assert.Equal(t, "-125", EvalInterp("(-5)^3", es).ToString())
	assert.Equal(t, "-125^-1", EvalInterp("(-5)^-3", es).ToString())

	//assert.Equal(t, "59049", EvalInterp("9.^5.", es).ToString())
}
