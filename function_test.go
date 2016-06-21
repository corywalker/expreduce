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
}
