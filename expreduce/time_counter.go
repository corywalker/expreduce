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

func (tc *TimeCounter) Update(other *TimeCounter) {
	for k, v := range other.times {
		tc.AddTime(k, v)
	}
}

func (tc *TimeCounter) TruncatedString(numToPrint int) string {
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
			buffer.WriteString(fmt.Sprintf("%v, %v\n", k, s))
			numPrinted++
		}
	}
	return buffer.String()
}

func (tc *TimeCounter) String() string {
	return tc.TruncatedString(25)
}

// TimeCounterGroup

type CounterGroupType uint8

const (
	CounterGroupDefTime CounterGroupType = iota + 1
	CounterGroupLhsDefTime
	CounterGroupEvalTime
	CounterGroupHeadEvalTime
)

type TimeCounterGroup struct {
	defTimeCounter TimeCounter
	lhsDefTimeCounter TimeCounter
	evalTimeCounter TimeCounter
	headEvalTimeCounter TimeCounter
}

func (tcg *TimeCounterGroup) Init() {
	tcg.defTimeCounter.Init()
	tcg.lhsDefTimeCounter.Init()
	tcg.evalTimeCounter.Init()
	tcg.headEvalTimeCounter.Init()
}

func (tcg *TimeCounterGroup) AddTime(counter CounterGroupType, key string, elapsed float64) {
	if counter == CounterGroupDefTime {
		tcg.defTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupLhsDefTime {
		tcg.lhsDefTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupEvalTime {
		tcg.evalTimeCounter.AddTime(key, elapsed)
	} else if counter == CounterGroupHeadEvalTime {
		tcg.headEvalTimeCounter.AddTime(key, elapsed)
	}
}

func (tcg *TimeCounterGroup) Update(other *TimeCounterGroup) {
	tcg.defTimeCounter.Update(&other.defTimeCounter)
	tcg.lhsDefTimeCounter.Update(&other.lhsDefTimeCounter)
	tcg.evalTimeCounter.Update(&other.evalTimeCounter)
	tcg.headEvalTimeCounter.Update(&other.headEvalTimeCounter)
}

func (tcg *TimeCounterGroup) String() string {
	var buffer bytes.Buffer
	buffer.WriteString(tcg.defTimeCounter.String() + "\n")
	buffer.WriteString(tcg.lhsDefTimeCounter.String() + "\n")
	buffer.WriteString(tcg.evalTimeCounter.String() + "\n")
	buffer.WriteString(tcg.headEvalTimeCounter.String() + "\n")
	return buffer.String()
}
