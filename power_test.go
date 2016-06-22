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
	assert.Equal(t, t9.ToString(), "x^2")
	assert.Equal(t, t10.ToString(), "x^(-1 + 3)")
	assert.Equal(t, t11.ToString(), "x^3")
	assert.Equal(t, "EQUAL_TRUE", t9.IsEqual(t10, es))
	assert.Equal(t, "EQUAL_UNK", t9.IsEqual(t11, es))
}
