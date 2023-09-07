package main

import (
	"bufio"
	"bytes"
	"flag"
	"fmt"
	"log"
	"net/http"
	_ "net/http/pprof"
	"os"
	"runtime/pprof"

	"github.com/corywalker/expreduce/expreduce"
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"gopkg.in/readline.v1"
)

var debug = flag.Bool("debug", false, "Debug mode. No initial definitions.")

var rawterm = flag.Bool(
	"rawterm",
	false,
	"Do not use readline. Useful for pexpect integration.",
)
var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to file")

var netprofile = flag.Bool(
	"netprofile",
	false,
	"Enable live profiling at http://localhost:8080/debug/pprof/",
)
var scriptfile = flag.String("script", "", "script `file` to read from")
var initfile = flag.String("initfile", "", "A script to run on initialization.")

var preloadRubi = flag.Bool(
	"preloadrubi",
	false,
	"Preload the Rubi definitions for integral support on startup.",
)

func main() {
	flag.Parse()

	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err != nil {
			log.Fatal(err)
		}
		if err := pprof.StartCPUProfile(f); err != nil {
			log.Fatal(err)
		}
		defer pprof.StopCPUProfile()
	}
	if *netprofile {
		//nolint:errcheck
		go http.ListenAndServe(":8080", nil)
	}

	fmt.Printf("Welcome to Expreduce!\n\n")

	es := expreduce.NewEvalState()
	if *preloadRubi {
		fmt.Println(
			"Pre-loading Rubi snapshot for integral support. Disable with -preloadrubi=false.",
		)
		es.Eval(atoms.E(atoms.S("LoadRubiBundledSnapshot")))
		fmt.Println("Done loading Rubi snapshot.")
		fmt.Print("\n")
	}
	if *debug {
		es.NoInit = true
		es.ClearAll()
	}

	if *initfile != "" {
		f, err := os.Open(*initfile)
		if err != nil {
			log.Fatal(err)
		}
		defer f.Close()

		buf := new(bytes.Buffer)
		if _, err := buf.ReadFrom(f); err != nil {
			log.Fatal(err)
		}
		scriptText := buf.String()
		expreduce.EvalInterpMany(scriptText, *initfile, es)
	}

	if *scriptfile != "" {
		f, err := os.Open(*scriptfile)
		if err != nil {
			log.Fatal(err)
		}
		defer f.Close()

		buf := new(bytes.Buffer)
		if _, err := buf.ReadFrom(f); err != nil {
			log.Fatal(err)
		}
		scriptText := buf.String()
		scriptSession(es, scriptText, *scriptfile)
	} else {
		interactiveSession(es)
	}
}

func scriptSession(es *expreduce.EvalState, srcText string, srcPath string) {
	exp := expreduce.EvalInterpMany(srcText, srcPath, es)
	res := es.Eval(exp)
	es.ProcessTopLevelResult(res, res)
}

func interactiveSession(es *expreduce.EvalState) {
	rl, err := readline.NewEx(&readline.Config{
		HistoryFile:         "/tmp/readline.tmp",
		ForceUseInteractive: true,
	})
	if err != nil {
		panic(err)
	}
	defer rl.Close()

	promptNum := 1
	for {
		line := ""
		var err error
		if *rawterm {
			reader := bufio.NewReader(os.Stdin)
			fmt.Printf("In[%d]:= ", promptNum)
			line, err = reader.ReadString('\n')
		} else {
			rl.SetPrompt(fmt.Sprintf("In[%d]:= ", promptNum))
			line, err = rl.Readline()
		}
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}
		if line == "" {
			continue
		}
		fmt.Printf("\n")

		exp := parser.Interp(line, es)
		res := es.Eval(exp)
		res = es.ProcessTopLevelResult(exp, res)

		printFormattedOutput(es, res, promptNum)
		promptNum++
	}
}

func printFormattedOutput(
	es *expreduce.EvalState,
	res expreduceapi.Ex,
	promptNum int,
) {
	isNull := false
	asSym, isSym := res.(*atoms.Symbol)
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
			asSpecialForm, isSpecialForm := atoms.HeadAssertion(
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
}
