package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestComparison(t *testing.T) {

	fmt.Println("Testing comparison")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("9*x==x*9", es).ToString())
	assert.Equal(t, "False", EvalInterp("9*x==x*10", es).ToString())
	assert.Equal(t, "5", EvalInterp("tmp=5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).ToString())
	assert.Equal(t, "True", EvalInterp("5==tmp", es).ToString())
	assert.Equal(t, "False", EvalInterp("tmp==6", es).ToString())
	assert.Equal(t, "False", EvalInterp("6==tmp", es).ToString())

	assert.Equal(t, "False", EvalInterp("a===b", es).ToString())
	assert.Equal(t, "True", EvalInterp("a===a", es).ToString())
	assert.Equal(t, "a==b", EvalInterp("a==b", es).ToString())
	assert.Equal(t, "True", EvalInterp("a==a", es).ToString())
	assert.Equal(t, "a==2", EvalInterp("a==2", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp===5", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5.", es).ToString())
	assert.Equal(t, "True", EvalInterp("tmp==5.00000", es).ToString())
	assert.Equal(t, "False", EvalInterp("tmp===5.", es).ToString())
	assert.Equal(t, "True", EvalInterp("1+1==2", es).ToString())
	assert.Equal(t, "True", EvalInterp("1+1===2", es).ToString())
	assert.Equal(t, "y==m*x+b", EvalInterp("y==m*x+b", es).ToString())
	assert.Equal(t, "False", EvalInterp("y===m*x+b", es).ToString())

	// Future
	//assert.Equal(t, "False", EvalInterp("4/3==3/2", es).ToString())
	//assert.Equal(t, "True", EvalInterp("4/3==8/6", es).ToString())
}
