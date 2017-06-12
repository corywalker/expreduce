package expreduce

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func newPf(startI int, endI int) parsedForm {
	return parsedForm{
		startI, endI,
		nil, nil,
		false, false, false,
	}
}

func TestAllocations(t *testing.T) {
	fmt.Println("Testing allocations")

	forms := []parsedForm{
		newPf(1, 2),
		newPf(0, 1),
		newPf(0, 99999),
	}
	ai := NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 0, 3}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 0, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 1, 1}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 3}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 1),
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 99999),
		newPf(1, 1),
		newPf(0, 99999),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0, 1, 3}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{1, 1, 2}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{2, 1, 1}, ai.alloc)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{3, 1, 0}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 99999),
	}
	ai = NewAllocIter(0, forms)
	assert.Equal(t, true, ai.next())
	assert.Equal(t, []int{0}, ai.alloc)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(1, 99999),
	}
	ai = NewAllocIter(0, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(5, 5),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(1, 1),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	// Impossible configuration. Should return false immediately.
	forms = []parsedForm{
		newPf(5, 0),
	}
	ai = NewAllocIter(4, forms)
	assert.Equal(t, false, ai.next())

	forms = []parsedForm{
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
	}
	ai = NewAllocIter(800000, forms)
	num := 0
	for num = 0; ai.next(); num++ {}
	assert.Equal(t, 800000, num)

	// should be 1/2 n (1+n)/.n->(ncomps-1)
	forms = []parsedForm{
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
		newPf(1, 1),
		newPf(0, 999999),
	}
	ai = NewAllocIter(1400, forms)
	for num = 0; ai.next(); num++ {}
	assert.Equal(t, 979300, num)
}
