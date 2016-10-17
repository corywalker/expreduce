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
	assert.Equal(t, "Error[\"First error\"]", a.String())
	b = &Expression{[]Ex{&Symbol{"Error"}, &String{"Second error"}}}
	assert.Equal(t, "Error[\"Second error\"]", b.String())
	assert.Equal(t, "EQUAL_TRUE", a.IsEqual(a, &es.CASLogger))
	assert.Equal(t, "EQUAL_TRUE", b.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", a.IsEqual(b, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", b.IsEqual(a, &es.CASLogger))
}
