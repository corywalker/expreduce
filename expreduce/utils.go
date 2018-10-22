package expreduce

import (
	"bytes"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func ExArrayToString(exArray []expreduceapi.Ex, es expreduceapi.EvalStateInterface) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	for i, e := range exArray {
		buffer.WriteString(e.String(es))
		if i != len(exArray)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("}")
	return buffer.String()
}

func ExArrayDeepCopy(exArray []expreduceapi.Ex) []expreduceapi.Ex {
	res := make([]expreduceapi.Ex, len(exArray))
	for i, e := range exArray {
		res[i] = e.DeepCopy()
	}
	return res
}

func Max(x, y int) int {
	if x > y {
		return x
	}
	return y
}

func Min(x, y int) int {
	if x < y {
		return x
	}
	return y
}
