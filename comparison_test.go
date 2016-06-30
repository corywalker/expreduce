package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("9*x==x*9", es).ToString())
	assert.Equal(t, "((9 * x)) == ((x * 10))", EvalInterp("9*x==x*10", es).ToString())
	assert.Equal(t, "5", EvalInterp("tmp=5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).ToString())
	assert.Equal(t, "True", EvalInterp("5==tmp", es).ToString())
	assert.Equal(t, "False", EvalInterp("tmp==6", es).ToString())
	assert.Equal(t, "False", EvalInterp("6==tmp", es).ToString())

	assert.Equal(t, "False", EvalInterp("a===b", es).ToString())
	assert.Equal(t, "True", EvalInterp("a===a", es).ToString())
	assert.Equal(t, "(a) == (b)", EvalInterp("a==b", es).ToString())
	assert.Equal(t, "True", EvalInterp("a==a", es).ToString())
	assert.Equal(t, "(a) == (2)", EvalInterp("a==2", es).ToString())
	assert.Equal(t, "(2) == (a)", EvalInterp("2==a", es).ToString())
	assert.Equal(t, "(2) == ((a + b))", EvalInterp("2==a+b", es).ToString())
	assert.Equal(t, "(2.) == (a)", EvalInterp("2.==a", es).ToString())
	assert.Equal(t, "(2^k) == (a)", EvalInterp("2^k==a", es).ToString())
	assert.Equal(t, "(2^k) == (2^a)", EvalInterp("2^k==2^a", es).ToString())
	assert.Equal(t, "(2^k) == ((k + 2))", EvalInterp("2^k==k+2", es).ToString())
	assert.Equal(t, "(k) == ((2 * k))", EvalInterp("k==2*k", es).ToString())
	assert.Equal(t, "((2 * k)) == (k)", EvalInterp("2*k==k", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp===5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5.", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5.00000", es).ToString())
	assert.Equal(t, "False", EvalInterp("tmp===5.", es).ToString())
	assert.Equal(t, "True", EvalInterp("1+1==2", es).ToString())
	assert.Equal(t, "True", EvalInterp("1+1===2", es).ToString())
	assert.Equal(t, "(y) == (((m * x) + b))", EvalInterp("y==m*x+b", es).ToString())
	assert.Equal(t, "False", EvalInterp("y===m*x+b", es).ToString())

	assert.Equal(t, "True", EvalInterp("1==1.", es).ToString())
	assert.Equal(t, "False", EvalInterp("1===1.", es).ToString())
	assert.Equal(t, "True", EvalInterp("1.==1", es).ToString())
	assert.Equal(t, "False", EvalInterp("1.===1", es).ToString())

	assert.Equal(t, "True", EvalInterp("(x==2)==(x==2)", es).ToString())
	assert.Equal(t, "True", EvalInterp("(x==2.)==(x==2)", es).ToString())
	assert.Equal(t, "True", EvalInterp("(x===2.)==(x===2)", es).ToString())
	assert.Equal(t, "True", EvalInterp("(x===2.)===(x===2)", es).ToString())
	assert.Equal(t, "False", EvalInterp("(x==2.)===(x==2)", es).ToString())
	assert.Equal(t, "True", EvalInterp("If[xx == 2, yy, zz] == If[xx == 2, yy, zz]", es).ToString())
	assert.Equal(t, "True", EvalInterp("If[xx == 2, yy, zz] === If[xx == 2, yy, zz]", es).ToString())
	assert.Equal(t, "False", EvalInterp("If[xx == 2, yy, zz] === If[xx == 2., yy, zz]", es).ToString())
	assert.Equal(t, "False", EvalInterp("If[xx == 3, yy, zz] === If[xx == 2, yy, zz]", es).ToString())
	assert.Equal(t, "(If[(xx) == (3), yy, zz]) == (If[(xx) == (2), yy, zz])", EvalInterp("If[xx == 3, yy, zz] == If[xx == 2, yy, zz]", es).ToString())

	assert.Equal(t, "False", EvalInterp("(x == y) === (y == x)", es).ToString())
	assert.Equal(t, "True", EvalInterp("(x == y) === (x == y)", es).ToString())
	assert.Equal(t, "True", EvalInterp("(1 == 2) == (2 == 3)", es).ToString())
	assert.Equal(t, "False", EvalInterp("(1 == 2) == (2 == 2)", es).ToString())

	// Future
	//assert.Equal(t, "False", EvalInterp("4/3==3/2", es).ToString())
	//assert.Equal(t, "True", EvalInterp("4/3==8/6", es).ToString())
}
