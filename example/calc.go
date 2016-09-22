package main

import (
	"fmt"
	"github.com/corywalker/cas"
	"gopkg.in/readline.v1"
)

func main() {
	rl, err := readline.NewEx(&readline.Config{
		Prompt:      "> ",
		HistoryFile: "/tmp/readline.tmp",
	})
	if err != nil {
		panic(err)
	}
	defer rl.Close()

	es := cas.NewEvalState()
	//es.DebugOn()

	for {
		line, err := rl.Readline()
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}

		exp := cas.Interp(line)
		fmt.Printf("In:  %s\n", exp.ToString())
		//res := (&cas.BasicSimplify{exp.Eval(es)}).Eval(es).ToString()
		res := exp.Eval(es).ToString()
		fmt.Printf("Out: %s\n", res)
	}
}
