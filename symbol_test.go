package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestInterp(t *testing.T) {
	fmt.Println("Testing interp")

	es := NewEvalState()

	assert.Equal(t, "3", EasyRun("x=1+2", es))
	assert.Equal(t, "3", EasyRun("x", es))
	assert.Equal(t, "4", EasyRun("x+1", es))
	// To make sure the result does not change
	assert.Equal(t, "4", EasyRun("x+1", es))

	assert.Equal(t, "3", EasyRun("x=1+2", es))
	assert.Equal(t, "6", EasyRun("x*2", es))
	// To make sure the result does not change
	assert.Equal(t, "6", EasyRun("x=x*2", es))
	assert.Equal(t, "36", EasyRun("x=x*x", es))

	assert.Equal(t, "(a * a)", EasyRun("y=a*a", es))
	assert.Equal(t, "(a * a * a * a)", EasyRun("y=y*y", es))
	assert.Equal(t, "2", EasyRun("a=2", es))
	assert.Equal(t, "16", EasyRun("y", es))

	// Test function definitions
	es.ClearAll()
	CasAssertSame(t, es, "Null", "testa[x_] := x*2")
	CasAssertSame(t, es, "Null", "testa[x_Integer] := x*3")
	CasAssertSame(t, es, "Null", "testa[x_Real] := x*4")
	CasAssertSame(t, es, "8.", "testa[2.]")
	CasAssertSame(t, es, "6", "testa[2]")
	CasAssertSame(t, es, "2 * k", "testa[k]")
	CasAssertSame(t, es, "Null", "testb[x_Real] := x*4")
	CasAssertSame(t, es, "Null", "testb[x_Integer] := x*3")
	CasAssertSame(t, es, "Null", "testb[x_] := x*2")
	CasAssertSame(t, es, "8.", "testb[2.]")
	CasAssertSame(t, es, "6", "testb[2]")
	CasAssertSame(t, es, "2 * k", "testb[k]")
	CasAssertSame(t, es, "testa", "testa")
	CasAssertSame(t, es, "testb", "testb")
	CasAssertSame(t, es, "Null", "testb[x_] := x*5")
	CasAssertSame(t, es, "5 * k", "testb[k]")
	CasAssertSame(t, es, "8.", "testb[2.]")
	CasAssertSame(t, es, "Null", "testb[x_Real + sym] := 5")
	CasAssertSame(t, es, "5", "testb[2.+sym]")
	CasAssertSame(t, es, "5", "testb[sym+2.]")
	CasAssertSame(t, es, "Null", "testb[x_Real + sym] := 6")
	CasAssertSame(t, es, "6", "testb[2.+sym]")
	CasAssertSame(t, es, "6", "testb[sym+2.]")

	es.ClearAll()
	//CasAssertSame(t, es, "2 * x", "testa[x_] = x*2")
	//CasAssertSame(t, es, "3 * x", "testa[x_Integer] = x*3")
	//CasAssertSame(t, es, "4 * x", "testa[x_Real] = x*4")
	//CasAssertSame(t, es, "8.", "testa[2.]")
	//CasAssertSame(t, es, "6", "testa[2]")
	//CasAssertSame(t, es, "2 * k", "testa[k]")
	//CasAssertSame(t, es, "4 * x", "testb[x_Real] = x*4")
	//CasAssertSame(t, es, "3 * x", "testb[x_Integer] = x*3")
	//CasAssertSame(t, es, "2 * x", "testb[x_] = x*2")
	//CasAssertSame(t, es, "8.", "testb[2.]")
	//CasAssertSame(t, es, "6", "testb[2]")
	//CasAssertSame(t, es, "2 * k", "testb[k]")
	//CasAssertSame(t, es, "testa", "testa")
	//CasAssertSame(t, es, "testb", "testb")
	//CasAssertSame(t, es, "Null", "testb[x_] = x*5")
	//CasAssertSame(t, es, "5 * k", "testb[k]")
	//CasAssertSame(t, es, "8.", "testb[2.]")
}
