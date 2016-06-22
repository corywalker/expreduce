package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	es := NewEvalState()

	var lhs Ex = &Times{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Symbol{"x"},
	}}
	var rhs Ex = &Times{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1e9)},
	}}
	var a Ex = &Equal{lhs, rhs}
	fmt.Println(a.ToString())
	var res Ex = a.Eval(es)
	fmt.Println(res.ToString())
	assert.Equal(t, "True", res.ToString())

	lhs = &Times{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Symbol{"x"},
	}}
	rhs = &Times{[]Ex{
		&Symbol{"x"},
		&Flt{big.NewFloat(1e10)},
	}}
	a = &Equal{lhs, rhs}
	fmt.Println(a.ToString())
	res = a.Eval(es)
	fmt.Println(res.ToString())
	assert.Equal(t, "False", res.ToString())
}
