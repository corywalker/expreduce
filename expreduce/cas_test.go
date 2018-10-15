package expreduce

import (
	"flag"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"regexp"
	"testing"
	"sync"
)

var testmodules = flag.String("testmodules", "",
	"A regexp of modules to test, otherwise test all modules.")
var excludemodules = flag.String("excludemodules", "dummypattern",
	"A regexp of modules to exclude, otherwise test all modules.")
var testsyms = flag.String("testsyms", "",
	"A regexp of symbols to test, otherwise test all symbols.")
var verbosetest = flag.Bool("verbosetest", false,
	"Print every test case that runs.")
var deftimings = flag.Bool("deftimings", false,
	"Show the time consuption aggregations for each definition.")

func TestIncludedModules(t *testing.T) {
	var testModEx = regexp.MustCompile(*testmodules)
	var excludeModEx = regexp.MustCompile(*excludemodules)
	var testSymEx = regexp.MustCompile(*testsyms)
	defSets := GetAllDefinitions()
	numTests := 0
	timeCounter := TimeCounterGroup{}
	timeCounter.Init()
	var mockT testing.T
	for _, defSet := range defSets {
		if !testModEx.MatchString(defSet.Name) {
			continue
		}
		if excludeModEx.MatchString(defSet.Name) {
			continue
		}
		fmt.Printf("Testing module %s\n", defSet.Name)
		es := NewEvalState()
		if *deftimings {
			es.SetProfiling(true)
		}
		for _, def := range defSet.Defs {
			if !testSymEx.MatchString(def.Name) {
				continue
			}
			EvalInterp(fmt.Sprintf("$Context = \"%s%sTestState`\"", defSet.Name, def.Name), es)
			def.AnnotateWithDynamic(es)
			td := TestDesc{
				module: defSet.Name,
				def:    def,
			}
			i := 0
			for _, test := range def.SimpleExamples {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.Run(t, es, td)
				i += 1
			}
			for _, test := range def.FurtherExamples {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.Run(t, es, td)
				i += 1
			}
			for _, test := range def.Tests {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.Run(t, es, td)
				i += 1
			}
			for _, test := range def.KnownFailures {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				if test.Run(&mockT, es, td) {
					fmt.Printf("Previously failing test is now passing: %v\n", test)
				}
				i += 1
			}
			/*for _, test := range def.KnownDangerous {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				fmt.Printf("Running %v\n", test)
				test.Run(t, es, td)
				i += 1
			}*/
			numTests += i
		}
		if *deftimings {
			timeCounter.Update(&es.timeCounter)
		}
	}
	fmt.Printf("Ran %v module tests.\n", numTests)
	if *deftimings {
		fmt.Println(timeCounter.String())
	}
}

func TestLowLevel(t *testing.T) {

	fmt.Println("Testing low-level structs")

	es := NewEvalState()

	lhs := NewExpression([]Ex{
		NewSymbol("System`Power"),
		NewExpression([]Ex{
			NewSymbol("System`Plus"),
			NewSymbol("Global`a"),
			NewSymbol("Global`b"),
			NewSymbol("Global`c"),
		}),
		NewInt(0),
	})
	rule := NewExpression([]Ex{
		NewSymbol("System`Rule"),
		NewExpression([]Ex{
			NewSymbol("System`Power"),
			NewExpression([]Ex{
				NewSymbol("System`Blank"),
			}),
			NewInt(0),
		}),
		NewInt(99),
	})
	for numi := 0; numi < 700000; numi++ {
		Replace(lhs, rule, es)
	}

	// Test basic float functionality
	var f *Flt = NewReal(big.NewFloat(5.5))
	assert.Equal(t, "5.5", f.String(es))
	f.Eval(es)
	assert.Equal(t, "5.5", f.String(es))

	// Test nested addition functionality
	var a = NewExpression([]Ex{
		NewSymbol("System`Plus"),
		NewExpression([]Ex{
			NewSymbol("System`Plus"),
			NewReal(big.NewFloat(80)),
			NewReal(big.NewFloat(3)),
		}),

		NewReal(big.NewFloat(2)),
		NewReal(big.NewFloat(2.5)),
	})

	// Test equality checking
	assert.Equal(t, "EQUAL_TRUE", (NewReal(big.NewFloat(99))).IsEqual(NewReal(big.NewFloat(99)), &es.CASLogger))
	assert.Equal(t, "EQUAL_FALSE", (NewReal(big.NewFloat(99))).IsEqual(NewReal(big.NewFloat(98)), &es.CASLogger))
	assert.Equal(t, "EQUAL_TRUE", (NewSymbol("System`x")).IsEqual(NewSymbol("System`x"), &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", (NewSymbol("System`x")).IsEqual(NewSymbol("System`X"), &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", (NewSymbol("System`x")).IsEqual(NewSymbol("System`y"), &es.CASLogger))

	// Test evaluation
	newa := a.Eval(es)
	assert.Equal(t, "87.5", newa.String(es))

	// Test basic Symbol functionality
	var v *Symbol = NewSymbol("System`x")
	assert.Equal(t, "x", v.String(es))
	v.Eval(es)
	assert.Equal(t, "x", v.String(es))

	assert.Equal(t, "(a + b + c + d + e + f)", EasyRun("a + b + c +d +e +f", es))
	assert.Equal(t, "(a*b*c*d*e*f)", EasyRun("a * b * c *d *e *f", es))

	CasAssertSame(t, es, "2", "iubjndxuier = 2")
	_, containsTest := es.defined.Get("Global`iubjndxuier")
	assert.True(t, containsTest)
	es.ClearAll()
	_, containsTest = es.defined.Get("Global`iubjndxuier")
	assert.False(t, containsTest)

	// Test raw recursion speed
	EvalInterp("DownValues[fib]={HoldPattern[fib[0]]->0,HoldPattern[fib[1]]->1,HoldPattern[fib[x_]]:>fib[x-1]+fib[x-2]}", es)
	EvalInterp("fib[25]", es)
}

func TestDeepCopy(t *testing.T) {
	fmt.Println("Testing deepcopy")

	// So that we can print the values. Not very necessary.
	es := NewEvalState()

	// Test deepcopy
	var t1 = NewSymbol("System`x")
	t2 := *t1
	t3 := t1.DeepCopy().(*Symbol)
	assert.Equal(t, "System`x", t1.Name)
	assert.Equal(t, "System`x", t2.Name)
	assert.Equal(t, "System`x", t3.Name)
	t2.Name = "y"
	t3.Name = "z"
	assert.Equal(t, "System`x", t1.Name)
	assert.Equal(t, "y", t2.Name)
	assert.Equal(t, "z", t3.Name)

	var t4 = NewReal(big.NewFloat(2))
	t5 := *t4
	t6 := t4.DeepCopy().(*Flt)
	assert.Equal(t, "2.", t4.String(es))
	assert.Equal(t, "2.", t5.String(es))
	assert.Equal(t, "2.", t6.String(es))
	t5.Val.Add(t5.Val, big.NewFloat(2))
	t6.Val.Add(t6.Val, big.NewFloat(3))
	assert.Equal(t, "4.", t4.String(es)) // Because we used the wrong copy method
	assert.Equal(t, "4.", t5.String(es))
	assert.Equal(t, "5.", t6.String(es))
}

func TestConcurrency(t *testing.T) {

	fmt.Println("Testing concurrency")

	es1 := NewEvalState()
	es2 := NewEvalState()

	CasAssertSame(t, es1, "3", "1+2")
	CasAssertSame(t, es2, "3", "1+2")

	var wg sync.WaitGroup

	// Test concurrent evals on different EvalStates.
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func (t *testing.T) {
			defer wg.Done()
			esTest := NewEvalState()
			CasAssertSame(t, esTest, "3", "1+2")
		}(t)
	}
	wg.Wait()

	// Test read-only concurrent evals on the same EvalState.
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func (t *testing.T, es *EvalState) {
			defer wg.Done()
			CasAssertSame(t, es, "2x", "D[x^2, x]")
		}(t, es1)
	}
	wg.Wait()

	// Test writing concurrent evals on the same EvalState.
	for i := 0; i < 1000; i++ {
		wg.Add(1)
		go func (t *testing.T, i int, es *EvalState) {
			defer wg.Done()
			EvalInterp(fmt.Sprintf("testVar := %v", i), es)
		}(t, i, es1)
	}
	wg.Wait()

	// Test concurrent MarkSeen.
	for i := 0; i < 1000; i++ {
		wg.Add(1)
		go func (t *testing.T, i int, es *EvalState) {
			defer wg.Done()
			es.MarkSeen("uniqueIdentifierForMarkSeen")
		}(t, i, es1)
	}
	wg.Wait()
}
