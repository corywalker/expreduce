package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestExponent(t *testing.T) {
	fmt.Println("Testing exponents")

	var t9 = &Exponent{
		&Variable{"x"},
		&Float{2},
	}
	var t10 = &Exponent{
		&Variable{"x"},
		&Add{[]Ex{&Float{-1}, &Float{3}}},
	}
	var t11 = &Exponent{
		&Variable{"x"},
		&Float{3},
	}
	assert.Equal(t, t9.ToString(), "x^2")
	assert.Equal(t, t10.ToString(), "x^(-1 + 3)")
	assert.Equal(t, t11.ToString(), "x^3")
	assert.Equal(t, "EQUAL_TRUE", t9.IsEqual(t10))
	assert.Equal(t, "EQUAL_UNK", t9.IsEqual(t11))
}
