package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("9*x==x*9", es).String())
	assert.Equal(t, "((9 * x)) == ((10 * x))", EvalInterp("9*x==x*10", es).String())
	assert.Equal(t, "5", EvalInterp("tmp=5", es).String())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).String())
	assert.Equal(t, "True", EvalInterp("5==tmp", es).String())
	assert.Equal(t, "False", EvalInterp("tmp==6", es).String())
	assert.Equal(t, "False", EvalInterp("6==tmp", es).String())

	assert.Equal(t, "False", EvalInterp("a===b", es).String())
	assert.Equal(t, "True", EvalInterp("a===a", es).String())
	assert.Equal(t, "(a) == (b)", EvalInterp("a==b", es).String())
	assert.Equal(t, "True", EvalInterp("a==a", es).String())
	assert.Equal(t, "(a) == (2)", EvalInterp("a==2", es).String())
	assert.Equal(t, "(2) == (a)", EvalInterp("2==a", es).String())
	assert.Equal(t, "(2) == ((a + b))", EvalInterp("2==a+b", es).String())
	assert.Equal(t, "(2.) == (a)", EvalInterp("2.==a", es).String())
	assert.Equal(t, "(2^k) == (a)", EvalInterp("2^k==a", es).String())
	assert.Equal(t, "(2^k) == (2^a)", EvalInterp("2^k==2^a", es).String())
	assert.Equal(t, "(2^k) == ((2 + k))", EvalInterp("2^k==k+2", es).String())
	assert.Equal(t, "(k) == ((2 * k))", EvalInterp("k==2*k", es).String())
	assert.Equal(t, "((2 * k)) == (k)", EvalInterp("2*k==k", es).String())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).String())
	assert.Equal(t, "True", EvalInterp("tmp===5", es).String())
	assert.Equal(t, "True", EvalInterp("tmp==5.", es).String())
	assert.Equal(t, "True", EvalInterp("tmp==5.00000", es).String())
	assert.Equal(t, "False", EvalInterp("tmp===5.", es).String())
	assert.Equal(t, "True", EvalInterp("1+1==2", es).String())
	assert.Equal(t, "True", EvalInterp("1+1===2", es).String())
	assert.Equal(t, "(y) == ((b + (m * x)))", EvalInterp("y==m*x+b", es).String())
	assert.Equal(t, "False", EvalInterp("y===m*x+b", es).String())

	assert.Equal(t, "True", EvalInterp("1==1.", es).String())
	assert.Equal(t, "False", EvalInterp("1===1.", es).String())
	assert.Equal(t, "True", EvalInterp("1.==1", es).String())
	assert.Equal(t, "False", EvalInterp("1.===1", es).String())

	assert.Equal(t, "True", EvalInterp("(x==2)==(x==2)", es).String())
	assert.Equal(t, "True", EvalInterp("(x==2.)==(x==2)", es).String())
	assert.Equal(t, "True", EvalInterp("(x===2.)==(x===2)", es).String())
	assert.Equal(t, "True", EvalInterp("(x===2.)===(x===2)", es).String())
	assert.Equal(t, "False", EvalInterp("(x==2.)===(x==2)", es).String())
	assert.Equal(t, "True", EvalInterp("If[xx == 2, yy, zz] == If[xx == 2, yy, zz]", es).String())
	assert.Equal(t, "True", EvalInterp("If[xx == 2, yy, zz] === If[xx == 2, yy, zz]", es).String())
	assert.Equal(t, "False", EvalInterp("If[xx == 2, yy, zz] === If[xx == 2., yy, zz]", es).String())
	assert.Equal(t, "False", EvalInterp("If[xx == 3, yy, zz] === If[xx == 2, yy, zz]", es).String())
	assert.Equal(t, "(If[(xx) == (3), yy, zz]) == (If[(xx) == (2), yy, zz])", EvalInterp("If[xx == 3, yy, zz] == If[xx == 2, yy, zz]", es).String())

	assert.Equal(t, "False", EvalInterp("(x == y) === (y == x)", es).String())
	assert.Equal(t, "True", EvalInterp("(x == y) === (x == y)", es).String())
	assert.Equal(t, "True", EvalInterp("(1 == 2) == (2 == 3)", es).String())
	assert.Equal(t, "False", EvalInterp("(1 == 2) == (2 == 2)", es).String())

	// Future
	assert.Equal(t, "False", EvalInterp("4/3==3/2", es).String())
	assert.Equal(t, "True", EvalInterp("4/3==8/6", es).String())

	CasAssertSame(t, es, "True", "MatchQ[2*x, c1_Integer*a_Symbol]")
	_, containsC1 := es.defined["c1"]
	assert.False(t, containsC1)
	CasAssertSame(t, es, "True", "MatchQ[2^x, base_Integer^pow_Symbol]")
	_, containsBase := es.defined["base"]
	assert.False(t, containsBase)
	CasAssertSame(t, es, "True", "MatchQ[2+x, c1_Integer+a_Symbol]")
	CasAssertSame(t, es, "True", "MatchQ[a + b, x_Symbol + y_Symbol]")
	CasAssertSame(t, es, "False", "MatchQ[a + b, x_Symbol + x_Symbol]")
	CasAssertSame(t, es, "True", "MatchQ[{a,b}, {x_Symbol,y_Symbol}]")
	CasAssertSame(t, es, "False", "MatchQ[{a,b}, {x_Symbol,x_Symbol}]")
	CasAssertSame(t, es, "True", "MatchQ[{2^a, a}, {2^x_Symbol, x_Symbol}]")
	CasAssertSame(t, es, "False", "MatchQ[{2^a, b}, {2^x_Symbol, x_Symbol}]")
}
