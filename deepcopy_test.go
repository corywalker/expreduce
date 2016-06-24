package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
)

func TestDeepCopy(t *testing.T) {
	fmt.Println("Testing deepcopy")

	//es := NewEvalState()

	// Sanity check
	var t1 = &Symbol{"x"}
	t2 := *t1
	t3 := t1.DeepCopy().(*Symbol)
	assert.Equal(t, "x", t1.Name)
	assert.Equal(t, "x", t2.Name)
	assert.Equal(t, "x", t3.Name)
	t2.Name = "y"
	t3.Name = "z"
	assert.Equal(t, "x", t1.Name)
	assert.Equal(t, "y", t2.Name)
	assert.Equal(t, "z", t3.Name)

	var t4 = &Flt{big.NewFloat(2)}
	t5 := *t4
	t6 := t4.DeepCopy().(*Flt)
	assert.Equal(t, "2.", t4.ToString())
	assert.Equal(t, "2.", t5.ToString())
	assert.Equal(t, "2.", t6.ToString())
	t5.Val.Add(t5.Val, big.NewFloat(2))
	t6.Val.Add(t6.Val, big.NewFloat(3))
	assert.Equal(t, "4.", t4.ToString()) // Because we used the wrong copy method
	assert.Equal(t, "4.", t5.ToString())
	assert.Equal(t, "5.", t6.ToString())
}
