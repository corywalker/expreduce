package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	var lhs Ex = &Mul{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Variable{"x"},
	}}
	var rhs Ex = &Mul{[]Ex{
		&Variable{"x"},
		&Flt{big.NewFloat(1e9)},
	}}
	var a Ex = &EqualQ{lhs, rhs}
	fmt.Println(a.ToString())
	var res Ex = a.Eval()
	fmt.Println(res.ToString())
	assert.Equal(t, "true", res.ToString())

	lhs = &Mul{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Variable{"x"},
	}}
	rhs = &Mul{[]Ex{
		&Variable{"x"},
		&Flt{big.NewFloat(1e10)},
	}}
	a = &EqualQ{lhs, rhs}
	fmt.Println(a.ToString())
	res = a.Eval()
	fmt.Println(res.ToString())
	assert.Equal(t, "false", res.ToString())
}
