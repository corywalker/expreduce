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

	var t9 = &Expression{[]Ex{
		&Symbol{"Power"},
		&Symbol{"x"},
		&Flt{big.NewFloat(2)},
	}}
	var t10 = &Expression{[]Ex{
		&Symbol{"Power"},
		&Symbol{"x"},
		&Expression{[]Ex{&Symbol{"Plus"}, &Flt{big.NewFloat(-1)}, &Flt{big.NewFloat(3)}}},
	}}
	var t11 = &Expression{[]Ex{
		&Symbol{"Power"},
		&Symbol{"x"},
		&Flt{big.NewFloat(3)},
	}}
	assert.Equal(t, "x^2.", t9.StringForm("InputForm"))
	assert.Equal(t, "x^(-1. + 3.)", t10.StringForm("InputForm"))
	assert.Equal(t, "x^3.", t11.StringForm("InputForm"))
	assert.Equal(t, "EQUAL_TRUE", t9.IsEqual(t10.Eval(es), &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", t9.IsEqual(t11, &es.CASLogger))

	// Test raising expressions to the first power
	assert.Equal(t, "(1 + x)", EasyRun("(x+1)^1", es))
	assert.Equal(t, "0", EasyRun("0^1", es))
	assert.Equal(t, "0.", EasyRun("0.^1", es))
	assert.Equal(t, "-5", EasyRun("-5^1", es))
	assert.Equal(t, "-5.5", EasyRun("-5.5^1", es))
	assert.Equal(t, "(1 + x)", EasyRun("(x+1)^1.", es))
	assert.Equal(t, "0", EasyRun("0^1.", es))
	assert.Equal(t, "0.", EasyRun("0.^1.", es))
	assert.Equal(t, "-5", EasyRun("(-5)^1.", es))
	assert.Equal(t, "-5.5", EasyRun("-5.5^1.", es))

	// Test raising expressions to the zero power
	assert.Equal(t, "1", EasyRun("(x+1)^0", es))
	assert.Equal(t, "Indeterminate", EasyRun("0^0", es))
	assert.Equal(t, "Indeterminate", EasyRun("0.^0", es))
	assert.Equal(t, "-1", EasyRun("-5^0", es))
	assert.Equal(t, "1", EasyRun("(-5)^0", es))
	assert.Equal(t, "1", EasyRun("(-5.5)^0", es))
	assert.Equal(t, "1", EasyRun("(x+1)^0.", es))
	assert.Equal(t, "Indeterminate", EasyRun("0^0.", es))
	assert.Equal(t, "Indeterminate", EasyRun("0.^0.", es))
	assert.Equal(t, "-1", EasyRun("-5^0.", es))
	assert.Equal(t, "1", EasyRun("(-5.5)^0.", es))
	assert.Equal(t, "-1", EasyRun("-5^0", es))
	assert.Equal(t, "1", EasyRun("99^0", es))

	assert.Equal(t, "125", EasyRun("5^3", es))
	assert.Equal(t, "1/125", EasyRun("5^-3", es))
	assert.Equal(t, "-125", EasyRun("(-5)^3", es))
	assert.Equal(t, "-1/125", EasyRun("(-5)^-3", es))

	//assert.Equal(t, "2.975379863266329e+1589", EasyRun("39^999.", es))
	//assert.Equal(t, "3.360915398890324e-1590", EasyRun("39^-999.", es))
	//assert.Equal(t, "1.9950631168791027e+3010", EasyRun(".5^-10000.", es))
	//assert.Equal(t, "1.9950631168791027e+3010", EasyRun(".5^-10000", es))
	assert.Equal(t, "2.97538e+1589", EasyRun("39^999.", es))
	assert.Equal(t, "3.36092e-1590", EasyRun("39^-999.", es))
	assert.Equal(t, "1.99506e+3010", EasyRun(".5^-10000.", es))
	assert.Equal(t, "1.99506e+3010", EasyRun(".5^-10000", es))

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

	es.ClearAll()
	CasAssertSame(t, es, "Rational", "Power[2, -1] // Head")
	CasAssertSame(t, es, "Integer", "Power[1, -1] // Head")
	CasAssertSame(t, es, "Integer", "Power[2, 2] // Head")
	CasAssertSame(t, es, "Rational", "Power[-2, -1] // Head")
	CasAssertSame(t, es, "Rational", "Power[2, -2] // Head")

	// Text Expand
	CasAssertSame(t, es, "Null", "f[n_, m_] := Sum[KroneckerDelta[m - Sum[r[i], {i, n}]] (Multinomial @@ Sequence@Array[r, n]) Product[x[i]^r[i], {i, n}], Evaluate@(Sequence @@ Table[{r[i], 0, m}, {i, 1, n}])]")
	CasAssertSame(t, es, "x[1]^3 + 3 (x[1]^2)*x[2] + 3 x[1]*(x[2]^2) + x[2]^3", "f[2,3]")
	//CasAssertSame(t, es, "Null", "myexpand[(Plus[addends__])^(mmatch_Integer)] := Sum[KroneckerDelta[mmatch - Sum[r[i], {i, Length[{addends}]}]]*Multinomial @@ Sequence[Array[r, Length[{addends}]]]*Product[x[i]^r[i], {i, Length[{addends}]}], Evaluate[Sequence @@ Table[{r[i], 0, mmatch}, {i, 1, Length[{addends}]}]]]")
	//CasAssertSame(t, es, "x[1]^3 + 3 (x[1]^2)*x[2] + 3 x[1]*(x[2]^2) + x[2]^3", "myexpand[(y[1] + y[2])^3]")
}
