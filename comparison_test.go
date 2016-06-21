package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	var es EvalState

	var lhs Ex = &Mul{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Symbol{"x"},
	}}
	var rhs Ex = &Mul{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1e9)},
	}}
	var a Ex = &EqualQ{lhs, rhs}
	fmt.Println(a.ToString())
	var res Ex = a.Eval(es)
	fmt.Println(res.ToString())
	assert.Equal(t, "True", res.ToString())

	lhs = &Mul{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Symbol{"x"},
	}}
	rhs = &Mul{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1e10)},
	}}
	a = &EqualQ{lhs, rhs}
	fmt.Println(a.ToString())
	res = a.Eval(es)
	fmt.Println(res.ToString())
	assert.Equal(t, "False", res.ToString())
}
