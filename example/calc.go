package main

import (
	"fmt"
	"flag"
	"github.com/corywalker/cas"
	"gopkg.in/readline.v1"
)

func main() {
	var debug = flag.Bool("debug", false, "Debug mode. No initial definitions.")
	flag.Parse()

	rl, err := readline.NewEx(&readline.Config{
		Prompt:      "> ",
		HistoryFile: "/tmp/readline.tmp",
	})
	if err != nil {
		panic(err)
	}
	defer rl.Close()

	es := cas.NewEvalState()
	if *debug {
		es.NoInit = true
		es.ClearAll()
	}
	//es.DebugOn()

	for {
		line, err := rl.Readline()
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}

		exp := cas.Interp(line)
		fmt.Printf("In:  %s\n", exp)
		res := exp.Eval(es)
		fmt.Printf("Out: %s\n", res)
	}
}
