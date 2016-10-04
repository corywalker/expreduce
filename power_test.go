package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
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
		&Expression{[]Ex{&Symbol{"Plus"}, &Flt{big.NewFloat(-1)}, &Flt{big.NewFloat(3)}}},
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

	assert.Equal(t, "2.975379863266329e+1589", EvalInterp("39^999.", es).ToString())
	assert.Equal(t, "3.360915398890324e-1590", EvalInterp("39^-999.", es).ToString())
	assert.Equal(t, "1.9950631168791027e+3010", EvalInterp(".5^-10000.", es).ToString())
	assert.Equal(t, "1.9950631168791027e+3010", EvalInterp(".5^-10000", es).ToString())

	es.ClearAll()
	assert.Equal(t, "1", EasyRun("1^1", es))
	assert.Equal(t, "1", EasyRun("1^2", es))
	assert.Equal(t, "1", EasyRun("1^0", es))
	assert.Equal(t, "1", EasyRun("1^-1", es))
	assert.Equal(t, "1", EasyRun("1^-2", es))
	assert.Equal(t, "1", EasyRun("1^99999992", es))
	assert.Equal(t, "1.", EasyRun("1^2.", es))
	assert.Equal(t, "1.", EasyRun("1^99999992.", es))
	assert.Equal(t, "1.", EasyRun("1.^30", es))
	assert.Equal(t, "4.", EasyRun("(1.*2*1.)^2", es))
	assert.Equal(t, "-1", EasyRun("(-1)^1", es))
	assert.Equal(t, "1", EasyRun("(-1)^2", es))
	assert.Equal(t, "1", EasyRun("(-1)^0", es))
	assert.Equal(t, "1", EasyRun("(-1)^0", es))
	assert.Equal(t, "-1", EasyRun("(-1)^-1", es))
	assert.Equal(t, "1", EasyRun("(-1)^-2", es))
	assert.Equal(t, "1", EasyRun("(-1)^99999992", es))
	assert.Equal(t, "1.", EasyRun("(-1.)^30", es))
	assert.Equal(t, "4.", EasyRun("(1.*2*-1.)^2", es))
	assert.Equal(t, "-0.5", EasyRun("(1.*2*-1.)^(-1)", es))
}
