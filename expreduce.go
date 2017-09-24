package main

import (
	"flag"
	"fmt"
	"github.com/corywalker/expreduce/expreduce"
	"gopkg.in/readline.v1"
	"log"
	"os"
	"runtime/pprof"
	"net/http"
	_ "net/http/pprof"
)

var debug = flag.Bool("debug", false, "Debug mode. No initial definitions.")
var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to file")
var netprofile = flag.Bool("netprofile", false, "Enable live profiling at http://localhost:8080/debug/pprof/")

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
	if *netprofile {
		go http.ListenAndServe(":8080", nil)
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
		res = es.ProcessTopLevelResult(res)

		isNull := false
		asSym, isSym := res.(*expreduce.Symbol)
		if isSym {
			if asSym.Name == "System`Null" {
				isNull = true
			}
		}

		if !isNull {
			// Print formatted result
			specialForms := []string{
				"System`FullForm",
				"System`OutputForm",
			}
			wasSpecialForm := false
			for _, specialForm := range specialForms {
				asSpecialForm, isSpecialForm := expreduce.HeadAssertion(
					res, specialForm)
				if !isSpecialForm {
					continue
				}
				if len(asSpecialForm.Parts) != 2 {
					continue
				}
				fmt.Printf(
					"Out[%d]//%s= %s\n\n",
					promptNum,
					specialForm[7:],
					asSpecialForm.Parts[1].StringForm(
						expreduce.ActualStringFormArgsFull(specialForm[7:], es)),
				)
				wasSpecialForm = true
			}
			if !wasSpecialForm {
				fmt.Printf("Out[%d]= %s\n\n", promptNum, res.StringForm(
					expreduce.ActualStringFormArgsFull("InputForm", es)))
			}
		}

		promptNum += 1
	}
}
