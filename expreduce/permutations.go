package expreduce

// A Simple, Efficient P(n,k) Algorithm by Alistair Israel
// http://alistairisrael.wordpress.com/2009/09/22/simple-efficient-pnk-algorithm/
// Go implementation in 2016 by Cory Walker

func swap(ar []int, first int, second int) {
	ar[first], ar[second] = ar[second], ar[first]
}

func reverse(ar []int) {
	for i, j := 0, len(ar)-1; i < j; i, j = i+1, j-1 {
		swap(ar, i, j)
	}
}

func nextKPermutation(ar []int, n int, k int) int {
	if (k <= 0) {
		return 0
	}

	var i int
	var j int
	edge := k - 1

	if k < n {
		j = k
		// search for largest j such that a_j > a_edge (a is increasing for j>=k)
		// This is the reason why k cannot be zero, since edge = k-1.
		for j < n && ar[edge] >= ar[j] {
			j++
		}
	}
	if k < n && j < n {
		swap(ar, edge, j)
	} else {
		if k < n {
			// might be an issue here
			reverse(ar[k:])
		}

		// find rightmost ascent to left of edge
		i = edge - 1
		for i >= 0 && ar[i] >= ar[i+1] {
			i--
		}

		if i < 0 {
			return 0
		}

		// find smallest j>=i+1 where a_j>a_i (a is decreasing for j>=i+1)
		j = n - 1
		for j > i && ar[i] >= ar[j] {
			j--
		}

		swap(ar, i, j)

		// might be an issue here
		reverse(ar[i+1:])
	}

	return 1
}
