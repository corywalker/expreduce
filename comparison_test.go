package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	es := NewEvalState()

	assert.Equal(t, "True", EasyRun("9*x==x*9", es))
	assert.Equal(t, "((9 * x)) == ((10 * x))", EasyRun("9*x==x*10", es))
	assert.Equal(t, "5", EasyRun("tmp=5", es))
	assert.Equal(t, "True", EasyRun("tmp==5", es))
	assert.Equal(t, "True", EasyRun("5==tmp", es))
	assert.Equal(t, "False", EasyRun("tmp==6", es))
	assert.Equal(t, "False", EasyRun("6==tmp", es))

	assert.Equal(t, "False", EasyRun("a===b", es))
	assert.Equal(t, "True", EasyRun("a===a", es))
	assert.Equal(t, "(a) == (b)", EasyRun("a==b", es))
	assert.Equal(t, "True", EasyRun("a==a", es))
	assert.Equal(t, "(a) == (2)", EasyRun("a==2", es))
	assert.Equal(t, "(2) == (a)", EasyRun("2==a", es))
	assert.Equal(t, "(2) == ((a + b))", EasyRun("2==a+b", es))
	assert.Equal(t, "(2.) == (a)", EasyRun("2.==a", es))
	assert.Equal(t, "(2^k) == (a)", EasyRun("2^k==a", es))
	assert.Equal(t, "(2^k) == (2^a)", EasyRun("2^k==2^a", es))
	assert.Equal(t, "(2^k) == ((2 + k))", EasyRun("2^k==k+2", es))
	assert.Equal(t, "(k) == ((2 * k))", EasyRun("k==2*k", es))
	assert.Equal(t, "((2 * k)) == (k)", EasyRun("2*k==k", es))
	assert.Equal(t, "True", EasyRun("tmp==5", es))
	assert.Equal(t, "True", EasyRun("tmp===5", es))
	assert.Equal(t, "True", EasyRun("tmp==5.", es))
	assert.Equal(t, "True", EasyRun("tmp==5.00000", es))
	assert.Equal(t, "False", EasyRun("tmp===5.", es))
	assert.Equal(t, "True", EasyRun("1+1==2", es))
	assert.Equal(t, "True", EasyRun("1+1===2", es))
	assert.Equal(t, "(y) == ((b + (m * x)))", EasyRun("y==m*x+b", es))
	assert.Equal(t, "False", EasyRun("y===m*x+b", es))

	assert.Equal(t, "True", EasyRun("1==1.", es))
	assert.Equal(t, "False", EasyRun("1===1.", es))
	assert.Equal(t, "True", EasyRun("1.==1", es))
	assert.Equal(t, "False", EasyRun("1.===1", es))

	assert.Equal(t, "True", EasyRun("(x==2)==(x==2)", es))
	assert.Equal(t, "True", EasyRun("(x==2.)==(x==2)", es))
	assert.Equal(t, "True", EasyRun("(x===2.)==(x===2)", es))
	assert.Equal(t, "True", EasyRun("(x===2.)===(x===2)", es))
	assert.Equal(t, "False", EasyRun("(x==2.)===(x==2)", es))
	assert.Equal(t, "True", EasyRun("If[xx == 2, yy, zz] == If[xx == 2, yy, zz]", es))
	assert.Equal(t, "True", EasyRun("If[xx == 2, yy, zz] === If[xx == 2, yy, zz]", es))
	assert.Equal(t, "False", EasyRun("If[xx == 2, yy, zz] === If[xx == 2., yy, zz]", es))
	assert.Equal(t, "False", EasyRun("If[xx == 3, yy, zz] === If[xx == 2, yy, zz]", es))
	assert.Equal(t, "(If[(xx) == (3), yy, zz]) == (If[(xx) == (2), yy, zz])", EasyRun("If[xx == 3, yy, zz] == If[xx == 2, yy, zz]", es))

	assert.Equal(t, "False", EasyRun("(x == y) === (y == x)", es))
	assert.Equal(t, "True", EasyRun("(x == y) === (x == y)", es))
	assert.Equal(t, "True", EasyRun("(1 == 2) == (2 == 3)", es))
	assert.Equal(t, "False", EasyRun("(1 == 2) == (2 == 2)", es))

	// Future
	assert.Equal(t, "False", EasyRun("4/3==3/2", es))
	assert.Equal(t, "True", EasyRun("4/3==8/6", es))

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
