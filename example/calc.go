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
		Prompt:      "In[]:= ",
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

	fmt.Printf("Welcome to Expreduce!\n\n")
	promptNum := 1
	for {
		rl.SetPrompt(fmt.Sprintf("In[%d]:= ", promptNum))
		line, err := rl.Readline()
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}
		fmt.Printf("\n")

		exp := expreduce.Interp(line)
		res := exp.Eval(es)

		isNull := false
		asSym, isSym := res.(*expreduce.Symbol)
		if isSym {
			if asSym.Name == "Null" {
				isNull = true
			}
		}

		if !isNull {
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
					"Out[%d]//%s= %s\n\n",
					promptNum,
					specialForm,
					asSpecialForm.Parts[1].StringForm(specialForm),
				)
				wasSpecialForm = true
			}
			if !wasSpecialForm {
				fmt.Printf("Out[%d]= %s\n\n", promptNum, res.StringForm("InputForm"))
			}
		}

		promptNum += 1
	}
}
