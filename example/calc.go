package main

import (
	"flag"
	"fmt"
	"github.com/corywalker/expreduce/expreduce"
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

	es := expreduce.NewEvalState()
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

		exp := expreduce.Interp(line)
		fmt.Printf("In:  %s\n", exp.StringForm("InputForm"))
		res := exp.Eval(es)

		// Print formatted result
		specialForms := []string{
			"FullForm",
			"OutputForm",
		}
		wasSpecialForm := false
		for _, specialForm := range specialForms {
			asSpecialForm, isSpecialForm := expreduce.HeadAssertion(res, specialForm)
			if !isSpecialForm {
				continue
			}
			if len(asSpecialForm.Parts) != 2 {
				continue
			}
			fmt.Printf(
				"Out//%s: %s\n",
				specialForm,
				asSpecialForm.Parts[1].StringForm(specialForm),
			)
			wasSpecialForm = true
		}
		if !wasSpecialForm {
			fmt.Printf("Out: %s\n", res.StringForm("InputForm"))
		}
	}
}
