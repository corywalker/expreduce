package main

import (
	"fmt"
	"gopkg.in/readline.v1"
	"github.com/corywalker/cas"
)


func main() {
	rl, err := readline.NewEx(&readline.Config{
		Prompt: "> ",
		HistoryFile: "/tmp/readline.tmp",
	})
	if err != nil {
		panic(err)
	}
	defer rl.Close()

	var es cas.EvalState

	for {
		line, err := rl.Readline()
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}

		exp := cas.Interp(line)
		fmt.Printf( "In:  %s\n", exp.ToString() );
		fmt.Printf( "Out: %s\n", exp.Eval(es).ToString() );
	}
}
