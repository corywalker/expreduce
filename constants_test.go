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
	//assert.Equal(t, "(-1.0000000000000003e+360 * x)", res.String())
	assert.Equal(t, "(-1e+360. * x)", res.String())

	a = &Symbol{"True"}
	assert.Equal(t, "True", a.String())
	var b Ex = &Symbol{"False"}
	assert.Equal(t, "False", b.String())
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, &es.CASLogger))
	assert.Equal(t, "EQUAL_TRUE", b.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_FALSE", a.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_FALSE", b.IsEqual(a, &es.CASLogger))
	//fmt.Println(a.String())

	a = &Expression{[]Ex{&Symbol{"Error"}, &String{"First error"}}}
	assert.Equal(t, "Error[First error]", a.String())
	b = &Expression{[]Ex{&Symbol{"Error"}, &String{"Second error"}}}
	assert.Equal(t, "Error[Second error]", b.String())
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, &es.CASLogger))
	assert.Equal(t, "EQUAL_TRUE", b.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", a.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", b.IsEqual(a, &es.CASLogger))

	// Test String
	CasAssertSame(t, es, "\"Hello\"", "\"Hello\"")
	CasAssertSame(t, es, "True", "\"Hello\" == \"Hello\"")
	CasAssertSame(t, es, "False", "\"Hello\" == \"Hello world\"")

	// Test Rational
	assert.Equal(t, "10/7", EasyRun("Rational[10, 7]", es))
	assert.Equal(t, "5/3", EasyRun("Rational[10, 6]", es))
	assert.Equal(t, "Rational[x, 10]", EasyRun("Rational[x, 10]", es))
	assert.Equal(t, "10", EasyRun("Rational[100, 10]", es))
	assert.Equal(t, "-10", EasyRun("Rational[-100, 10]", es))
	assert.Equal(t, "10", EasyRun("Rational[-100, -10]", es))
	assert.Equal(t, "-5/3", EasyRun("Rational[-10, 6]", es))
	assert.Equal(t, "5/3", EasyRun("Rational[-10, -6]", es))
	assert.Equal(t, "0", EasyRun("Rational[0, 5]", es))
	assert.Equal(t, "Rational[0, n]", EasyRun("Rational[0, n]", es))
	assert.Equal(t, "Indeterminate", EasyRun("Rational[0, 0]", es))
	assert.Equal(t, "ComplexInfinity", EasyRun("Rational[1, 0]", es))
	assert.Equal(t, "ComplexInfinity", EasyRun("Rational[-1, 0]", es))
	assert.Equal(t, "ComplexInfinity", EasyRun("Rational[-1, -0]", es))
	assert.Equal(t, "Indeterminate", EasyRun("Rational[-0, -0]", es))
	assert.Equal(t, "Indeterminate", EasyRun("Rational[-0, 0]", es))

	// Rational matching and replacement
	CasAssertSame(t, es, "2/3", "test = Rational[2, 3]")
	CasAssertSame(t, es, "True", "MatchQ[test, 2/3]")
	CasAssertSame(t, es, "True", "MatchQ[test, Rational[a_Integer, b_Integer]]")
	CasAssertSame(t, es, "{2, 3}", "2/3 /. Rational[a_Integer, b_Integer] -> {a, b}")
	CasAssertSame(t, es, "2/3", "2/3 /. a_Integer/b_Integer -> {a, b}")
	CasAssertSame(t, es, "buzz[bar]", "foo[bar, 1/2] /. foo[base_, 1/2] -> buzz[base]")
	CasAssertSame(t, es, "buzz[bar]", "foo[bar, 1/2] /. foo[base_, Rational[1, 2]] -> buzz[base]")//
	CasAssertSame(t, es, "buzz[bar]", "foo[bar, Rational[1, 2]] /. foo[base_, 1/2] -> buzz[base]")//
	CasAssertSame(t, es, "buzz[bar]", "foo[bar, Rational[1, 2]] /. foo[base_, Rational[1, 2]] -> buzz[base]")
	CasAssertSame(t, es, "True", "MatchQ[1/2, Rational[1, 2]]")
	CasAssertSame(t, es, "True", "MatchQ[Rational[1, 2], 1/2]")
	CasAssertSame(t, es, "False", "Hold[Rational[1, 2]] === Hold[1/2]")
}
