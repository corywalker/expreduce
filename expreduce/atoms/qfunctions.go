package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func NumberQ(e expreduceapi.Ex) bool {
	_, ok := e.(*Integer)
	if ok {
		return true
	}
	_, ok = e.(*Flt)
	if ok {
		return true
	}
	_, ok = e.(*Rational)
	if ok {
		return true
	}
	_, ok = e.(*Complex)
	if ok {
		return true
	}
	return false
}
