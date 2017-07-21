package main

import (
	"flag"
	"fmt"
	"os"
	"runtime/pprof"
	"log"
	"github.com/corywalker/expreduce/expreduce"
	"gopkg.in/readline.v1"
)

var debug = flag.Bool("debug", false, "Debug mode. No initial definitions.")
var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to file")

func main() {
	flag.Parse()
	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err != nil {
			log.Fatal(err)
		}
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}

	rl, err := readline.NewEx(&readline.Config{
		HistoryFile:         "/tmp/readline.tmp",
		ForceUseInteractive: true,
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
		if line == "" {
			continue
		}
		fmt.Printf("\n")

		exp := expreduce.Interp(line, es)
		res := exp.Eval(es)

		isNull := false
		asSym, isSym := res.(*expreduce.Symbol)
		if isSym {
			if asSym.Name == "System`Null" {
				isNull = true
			}
		}

		if !isNull {
			// Print formatted result
			context, contextPath := expreduce.ActualStringFormArgs(es)
			specialForms := []string{
				"System`FullForm",
				"System`OutputForm",
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
					asSpecialForm.Parts[1].StringForm(specialForm, context, contextPath),
				)
				wasSpecialForm = true
			}
			if !wasSpecialForm {
				fmt.Printf("Out[%d]= %s\n\n", promptNum, res.StringForm("System`InputForm", context, contextPath))
			}
		}

		promptNum += 1
	}
}
