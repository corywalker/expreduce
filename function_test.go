package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestFunction(t *testing.T) {
	fmt.Println("Testing functions")

	es := NewEvalState()

	var t1 = &Function{
		"Power",
		[]Ex{
			&Flt{big.NewFloat(5)},
			&Flt{big.NewFloat(3)},
		},
	}
	assert.Equal(t, "Power[5., 3.]", t1.ToString())
	assert.Equal(t, "Power[5, 3]", Interp("Power[ 5,3 ]").ToString())
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
}
