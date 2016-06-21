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
	assert.Equal(t, t1.Name, "x")
	assert.Equal(t, t2.Name, "x")
	assert.Equal(t, t3.Name, "x")
	t2.Name = "y"
	t3.Name = "z"
	assert.Equal(t, t1.Name, "x")
	assert.Equal(t, t2.Name, "y")
	assert.Equal(t, t3.Name, "z")

	var t4 = &Flt{big.NewFloat(2)}
	t5 := *t4
	t6 := t4.DeepCopy().(*Flt)
	assert.Equal(t, t4.ToString(), "2")
	assert.Equal(t, t5.ToString(), "2")
	assert.Equal(t, t6.ToString(), "2")
	t5.Val.Add(t5.Val, big.NewFloat(2))
	t6.Val.Add(t6.Val, big.NewFloat(3))
	assert.Equal(t, t4.ToString(), "4") // Because we used the wrong copy method
	assert.Equal(t, t5.ToString(), "4")
	assert.Equal(t, t6.ToString(), "5")
}
