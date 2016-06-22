package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestFunction(t *testing.T) {
	fmt.Println("Testing functions")

	//es := NewEvalState()

	var t1 = &Function{
		"Power",
		[]Ex{
			&Flt{big.NewFloat(5)},
			&Flt{big.NewFloat(3)},
		},
	}
	assert.Equal(t, "Power[5, 3]", t1.ToString())
	assert.Equal(t, "Power[5, 3]", Interp("Power[ 5,3 ]").ToString())
	assert.Equal(t, "myfunc[]", Interp("myfunc[  ]").ToString())
	assert.Equal(t, "my2func[]", Interp("my2func[  ]").ToString())
}
