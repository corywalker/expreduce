package expreduce

import (
	"bytes"
	"fmt"
	"sort"
)

type TimeMap map[string]float64

type TimeCounter struct {
	times TimeMap
}

func (tc *TimeCounter) Init() {
	tc.times = make(TimeMap)
}

func (tc *TimeCounter) AddTime(key string, elapsed float64) {
	tc.times[key] += elapsed
}

func (tc *TimeCounter) String() string {
	var buffer bytes.Buffer
	n := map[float64][]string{}
	var a []float64
	for k, v := range tc.times {
		n[v] = append(n[v], k)
	}
	for k := range n {
		a = append(a, k)
	}
	sort.Sort(sort.Reverse(sort.Float64Slice(a)))
	for _, k := range a {
		for _, s := range n[k] {
			buffer.WriteString(fmt.Sprintf("%v, %v\n", k, s))
		}
	}
	return buffer.String()
}
