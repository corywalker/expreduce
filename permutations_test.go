package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestPermutations(t *testing.T) {
	fmt.Println("Testing permutations")

	// Test swap
	ar := []int{1, 2, 3}
	assert.Equal(t, []int{1, 2, 3}, ar)
	swap(ar, 1, 2)
	assert.Equal(t, []int{1, 3, 2}, ar)

	// Test reverse
	reverse(ar)
	assert.Equal(t, []int{2, 3, 1}, ar)
	ar2 := []int{0, 1}
	reverse(ar2)
	assert.Equal(t, []int{1, 0}, ar2)

	// Test nextKPermutation

	ar3, cont := []int{0, 1, 2}, 1
	assert.Equal(t, []int{0, 1, 2}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{0, 2, 1}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{1, 0, 2}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{1, 2, 0}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{2, 0, 1}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{2, 1, 0}, ar3)
	assert.Equal(t, 1, cont)

	// The algorithm should elect not to continue after this
	cont = nextKPermutation(ar3, 3, 2)
	assert.Equal(t, []int{2, 1, 0}, ar3)
	assert.Equal(t, 0, cont)

	// Test with k = 1
	ar3, cont = []int{0, 1, 2}, 1
	assert.Equal(t, []int{0, 1, 2}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 1)
	assert.Equal(t, []int{1, 0, 2}, ar3)
	assert.Equal(t, 1, cont)

	cont = nextKPermutation(ar3, 3, 1)
	assert.Equal(t, []int{2, 0, 1}, ar3)
	assert.Equal(t, 1, cont)

	// The algorithm should elect not to continue after this
	cont = nextKPermutation(ar3, 3, 1)
	assert.Equal(t, []int{2, 1, 0}, ar3)
	assert.Equal(t, 0, cont)
}
