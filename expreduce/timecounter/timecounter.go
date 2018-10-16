// Package timecounter provides functionality for aggregating times based on a
// string key.
package timecounter

import (
	"bytes"
	"fmt"
	"sort"
)

type timeMap map[string]float64
type countMap map[string]int64

type timeCounter struct {
	times  timeMap
	counts countMap
}

func (tc *timeCounter) Init() {
	tc.times = make(timeMap)
	tc.counts = make(countMap)
}

func (tc *timeCounter) AddTime(key string, elapsed float64) {
	tc.times[key] += elapsed
	tc.counts[key]++
}

func (tc *timeCounter) Update(other *timeCounter) {
	for k, v := range other.times {
		tc.AddTime(k, v)
	}
}

func (tc *timeCounter) TruncatedString(numToPrint int) string {
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
	numPrinted := 0
	for _, k := range a {
		if numPrinted >= numToPrint {
			break
		}
		for _, s := range n[k] {
			count := tc.counts[s]
			buffer.WriteString(fmt.Sprintf("%v, %v, %v\n", k, count, s))
			numPrinted++
		}
	}
	return buffer.String()
}

func (tc *timeCounter) String() string {
	return tc.TruncatedString(25)
}

// Group

type counterGroupType uint8

const (
	// CounterGroupDefTime is the counter for definition times.
	CounterGroupDefTime counterGroupType = iota + 1
	// CounterGroupLHSDefTime is the counter for LHS definition times.
	CounterGroupLHSDefTime
	// CounterGroupEvalTime is the counter for eval times.
	CounterGroupEvalTime
	// CounterGroupHeadEvalTime is the counter for head eval times.
	CounterGroupHeadEvalTime
)

// Group collects eval-related timeCounters.
type Group struct {
	defTimeCounter      timeCounter
	lhsDefTimeCounter   timeCounter
	evalTimeCounter     timeCounter
	headEvalTimeCounter timeCounter
}

// Init initializes the Group with empty maps.
func (tcg *Group) Init() {
	tcg.defTimeCounter.Init()
	tcg.lhsDefTimeCounter.Init()
	tcg.evalTimeCounter.Init()
	tcg.headEvalTimeCounter.Init()
}

// AddTime adds a floating-point time to a particular timeCounter, selected with
// a counterGroupType.
func (tcg *Group) AddTime(counter counterGroupType, key string, elapsed float64) {
	if counter == CounterGroupDefTime {
		tcg.defTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupLHSDefTime {
		tcg.lhsDefTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupEvalTime {
		tcg.evalTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupHeadEvalTime {
		tcg.headEvalTimeCounter.AddTime(key, elapsed)
	}
}

// Update adds another Group to this one.
func (tcg *Group) Update(other *Group) {
	tcg.defTimeCounter.Update(&other.defTimeCounter)
	tcg.lhsDefTimeCounter.Update(&other.lhsDefTimeCounter)
	tcg.evalTimeCounter.Update(&other.evalTimeCounter)
	tcg.headEvalTimeCounter.Update(&other.headEvalTimeCounter)
}

// Prints the counter group as a formatted string.
func (tcg *Group) String() string {
	var buffer bytes.Buffer
	buffer.WriteString(tcg.defTimeCounter.String() + "\n")
	buffer.WriteString(tcg.lhsDefTimeCounter.String() + "\n")
	buffer.WriteString(tcg.evalTimeCounter.String() + "\n")
	buffer.WriteString(tcg.headEvalTimeCounter.String() + "\n")
	return buffer.String()
}
