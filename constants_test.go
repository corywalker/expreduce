package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestConstants(t *testing.T) {

	fmt.Println("Testing constants")

	var a = &Mul{[]Ex{
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},
		&Flt{big.NewFloat(1e9)},

		&Flt{big.NewFloat(-1)},
		&Variable{"x"},
	}}
	var res Ex = a.Eval()
	assert.Equal(t, "(-1.0000000000000003e+360 * x)", res.ToString())
}
