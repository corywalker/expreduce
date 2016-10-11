package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"sort"
	"testing"
)

func TestExpression(t *testing.T) {
	fmt.Println("Testing expressions")

	es := NewEvalState()

	var t1 = &Expression{
		[]Ex{
			&Symbol{"Power"},
			&Flt{big.NewFloat(5)},
			&Flt{big.NewFloat(3)},
		},
	}
	assert.Equal(t, "5.^3.", t1.ToString())
	assert.Equal(t, "5^3", Interp("Power[ 5,3 ]").ToString())
	assert.Equal(t, "myfunc[]", Interp("myfunc[  ]").ToString())
	assert.Equal(t, "my2func[]", Interp("my2func[  ]").ToString())

	// Test comparison
	CasAssertSame(t, es, "True", "foo[x == 2, y, x] === foo[x == 2, y, x]")
	CasAssertSame(t, es, "False", "foo[x == 2, y, x] === foo[x == 2., y, x]")
	CasAssertSame(t, es, "True", "foo[x == 2, y, x] == foo[x == 2, y, x]")
	CasAssertSame(t, es, "True", "foo[x == 2, y, x] == foo[x == 2., y, x]")
	CasAssertSame(t, es, "foo[x == 2, y, x] == foo[x == 2., y, y]", "foo[x == 2, y, x] == foo[x == 2., y, y]")
	CasAssertSame(t, es, "False", "foo[x == 2, y, x] === foo[x == 2., y, y]")
	CasAssertSame(t, es, "foo[x == 2, y, x] == bar[x == 2, y, x]", "foo[x == 2, y, x] == bar[x == 2, y, x]")
	CasAssertSame(t, es, "False", "foo[x == 2, y, x] === bar[x == 2, y, x]")

	// Test replacement
	CasAssertSame(t, es, "foo[False, y, 5]", "foo[x == 2, y, x] /. x -> 5")
	CasAssertSame(t, es, "foo[5, y, x]", "foo[x * 2, y, x] /. x * 2 -> 5")
	CasAssertSame(t, es, "k", "foo[k] /. foo[k] -> k")
	CasAssertSame(t, es, "foo[k]", "foo[foo[k]] /. foo[k] -> k")
	CasAssertSame(t, es, "k", "(foo[foo[k]] /. foo[k] -> k) /. foo[k] -> k")
	CasAssertSame(t, es, "foo[bla]", "foo[foo[k]] /. foo[k] -> bla")

	// Test matching through expression arguments
	CasAssertSame(t, es, "True", "MatchQ[foo[2*x, x], foo[matcha_Integer*matchx_, matchx_]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[2*x, x], bar[matcha_Integer*matchx_, matchx_]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[2*x, y], foo[matcha_Integer*matchx_, matchx_]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[x, 2*y], foo[matcha_Integer*matchx_, matchx_]]")
	assert.Equal(t, "(foo[x, y, z]) == (foo[x, y])", EasyRun("foo[x, y, z] == foo[x, y]", es))
	assert.Equal(t, "(foo[x, y, z]) == (foo[x, y, 1])", EasyRun("foo[x, y, z] == foo[x, y, 1]", es))
	CasAssertSame(t, es, "True", "foo[x, y, 1] == foo[x, y, 1]")
	CasAssertSame(t, es, "True", "foo[x, y, 1.] == foo[x, y, 1]")
	CasAssertSame(t, es, "False", "foo[x, y, z] === foo[x, y]")
	CasAssertSame(t, es, "False", "foo[x, y, z] === foo[x, y, 1]")
	CasAssertSame(t, es, "True", "foo[x, y, 1] === foo[x, y, 1]")
	CasAssertSame(t, es, "False", "foo[x, y, 1.] === foo[x, y, 1]")

	// Test function evaluation
	es.ClearAll()
	CasAssertSame(t, es, "Null", "dist[x_, y_]:=(x^2 + y^2)^.5")
	CasAssertSame(t, es, "(j^2+k^2)^.5", "dist[j,k]")
	// Doesn't work due to round off error:
	//CasAssertSame(t, es, "5", "dist[3,4]")

	// Test BlankSequence matching
	es.ClearAll()
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[__Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[__]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[__Real]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1.], foo[__Real]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[], foo[__Real]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1.], foo[__]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1.], foo[___]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1.], foo[___Real]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1.], foo[___Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[], foo[___Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, __Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, 2, __Integer]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, 2]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2], foo[1, 2, 3]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, __Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, ___Integer]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, ___Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, ___Integer, 3]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 3]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 5]]")

	// Make sure some similar cases still work with Patterns, not just Blanks
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a__Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a___Integer]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, a___Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, a___Integer, 3]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 5]]")
	CasAssertSame(t, es, "False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b__Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b___Integer]]")
	CasAssertSame(t, es, "True", "MatchQ[foo[1, 2, 3, 4], foo[1, a__Integer, 3, b___Integer, 4]]")

	// Test replacement
	//CasAssertSame(t, es, "2 * a + 12 * b", "foo[1, 2, 3, 4] /. foo[1, amatch__Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]")
	//CasAssertSame(t, es, "a + 24 * b", "foo[1, 2, 3, 4] /. foo[1, amatch___Integer, bmatch___Integer] -> a*Times[amatch] + b*Times[bmatch]")

	// Test sort.Interface
	// Sort[foo[5., aa, 1.]] == foo[1., 5., aa]
	es.ClearAll()
	var exp = &Expression{
		[]Ex{
			&Symbol{"foo"},
			&Flt{big.NewFloat(5)},
			&Symbol{"aa"},
			&Flt{big.NewFloat(1)},
		},
	}
	assert.Equal(t, 3, exp.Len())
	// Should i sort before j?
	assert.Equal(t, false, exp.Less(0, 0))
	assert.Equal(t, true, exp.Less(0, 1))
	assert.Equal(t, true, exp.Less(2, 0))
	assert.Equal(t, true, exp.Less(2, 1))
	// Test the reverse of each
	assert.Equal(t, false, exp.Less(1, 0))
	assert.Equal(t, false, exp.Less(0, 2))
	assert.Equal(t, false, exp.Less(1, 2))
	// Test swap
	assert.Equal(t, "foo[5., aa, 1.]", exp.ToString())
	exp.Swap(0, 1)
	assert.Equal(t, "foo[aa, 5., 1.]", exp.ToString())
	sort.Sort(exp)
	assert.Equal(t, "foo[1., 5., aa]", exp.ToString())

	// Test Apply
	es.ClearAll()
	CasAssertSame(t, es, "foo[a,b,c]", "Apply[foo, {a,b,c}]")
}
