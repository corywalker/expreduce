package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestExponent(t *testing.T) {
	fmt.Println("Testing exponents")

	var t9 = &Exponent{
		&Symbol{"x"},
		&Flt{big.NewFloat(2)},
	}
	var t10 = &Exponent{
		&Symbol{"x"},
		&Add{[]Ex{&Flt{big.NewFloat(-1)}, &Flt{big.NewFloat(3)}}},
	}
	var t11 = &Exponent{
		&Symbol{"x"},
		&Flt{big.NewFloat(3)},
	}
	assert.Equal(t, t9.ToString(), "x^2")
	assert.Equal(t, t10.ToString(), "x^(-1 + 3)")
	assert.Equal(t, t11.ToString(), "x^3")
	assert.Equal(t, "EQUAL_TRUE", t9.IsEqual(t10))
	assert.Equal(t, "EQUAL_UNK", t9.IsEqual(t11))
}
