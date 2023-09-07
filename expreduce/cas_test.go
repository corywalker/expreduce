package expreduce

import (
	"flag"
	"fmt"
	"math/big"
	"regexp"
	"sync"
	"testing"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/stretchr/testify/assert"
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
	timeCounter := timecounter.Group{}
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
			EvalInterp(
				fmt.Sprintf(
					"$Context = \"%s%sTestState`\"",
					defSet.Name,
					def.Name,
				),
				es,
			)
			def.AnnotateWithDynamic(es)
			td := testDesc{
				module: defSet.Name,
				def:    def,
			}
			i := 0
			for _, test := range def.SimpleExamples {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.run(t, es, td)
				i++
			}
			for _, test := range def.FurtherExamples {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.run(t, es, td)
				i++
			}
			for _, test := range def.Tests {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				test.run(t, es, td)
				i++
			}
			for _, test := range def.KnownFailures {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				if *verbosetest {
					fmt.Println(test)
				}
				if test.run(&mockT, es, td) {
					fmt.Printf(
						"Previously failing test is now passing: %v\n",
						test,
					)
				}
				i++
			}
			/*for _, test := range def.KnownDangerous {
				td.desc = fmt.Sprintf("%s.%s #%d", defSet.Name, def.Name, i)
				fmt.Printf("Running %v\n", test)
				test.run(t, es, td)
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
	stringParams := ActualStringFormArgsFull("InputForm", es)

	lhs := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`Power"),
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Plus"),
			atoms.NewSymbol("Global`a"),
			atoms.NewSymbol("Global`b"),
			atoms.NewSymbol("Global`c"),
		}),

		atoms.NewInt(0),
	})

	rule := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`Rule"),
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Power"),
			atoms.NewExpression([]expreduceapi.Ex{
				atoms.NewSymbol("System`Blank"),
			}),

			atoms.NewInt(0),
		}),

		atoms.NewInt(99),
	})

	for numi := 0; numi < 700000; numi++ {
		replace(lhs, rule, es)
	}

	// Test basic float functionality
	var f *atoms.Flt = atoms.NewReal(big.NewFloat(5.5))
	assert.Equal(t, "5.5", f.StringForm(stringParams))
	es.Eval(f)
	assert.Equal(t, "5.5", f.StringForm(stringParams))

	// Test nested addition functionality
	var a = atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`Plus"),
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Plus"),
			atoms.NewReal(big.NewFloat(80)),
			atoms.NewReal(big.NewFloat(3)),
		}),

		atoms.NewReal(big.NewFloat(2)),
		atoms.NewReal(big.NewFloat(2.5)),
	})

	// Test equality checking
	assert.Equal(
		t,
		"EQUAL_TRUE",
		(atoms.NewReal(big.NewFloat(99))).IsEqual(
			atoms.NewReal(big.NewFloat(99)),
		),
	)
	assert.Equal(
		t,
		"EQUAL_FALSE",
		(atoms.NewReal(big.NewFloat(99))).IsEqual(
			atoms.NewReal(big.NewFloat(98)),
		),
	)
	assert.Equal(
		t,
		"EQUAL_TRUE",
		(atoms.NewSymbol("System`x")).IsEqual(atoms.NewSymbol("System`x")),
	)
	assert.Equal(
		t,
		"EQUAL_UNK",
		(atoms.NewSymbol("System`x")).IsEqual(atoms.NewSymbol("System`X")),
	)
	assert.Equal(
		t,
		"EQUAL_UNK",
		(atoms.NewSymbol("System`x")).IsEqual(atoms.NewSymbol("System`y")),
	)

	// Test evaluation
	newa := es.Eval(a)
	assert.Equal(t, "87.5", newa.StringForm(stringParams))

	// Test basic Symbol functionality
	var v *atoms.Symbol = atoms.NewSymbol("System`x")
	assert.Equal(t, "x", v.StringForm(stringParams))
	es.Eval(v)
	assert.Equal(t, "x", v.StringForm(stringParams))

	casAssertSame(t, es, "(a + b + c + d + e + f)", "a + b + c +d +e +f")
	casAssertSame(t, es, "(a*b*c*d*e*f)", "a * b * c *d *e *f")

	casAssertSame(t, es, "2", "iubjndxuier = 2")
	_, containsTest := es.GetDefinedMap().Get("Global`iubjndxuier")
	assert.True(t, containsTest)
	es.ClearAll()
	_, containsTest = es.GetDefinedMap().Get("Global`iubjndxuier")
	assert.False(t, containsTest)

	// Test raw recursion speed
	EvalInterp(
		"DownValues[fib]={HoldPattern[fib[0]]->0,HoldPattern[fib[1]]->1,HoldPattern[fib[x_]]:>fib[x-1]+fib[x-2]}",
		es,
	)
	EvalInterp("fib[25]", es)
}

func TestDeepCopy(t *testing.T) {
	fmt.Println("Testing deepcopy")

	// So that we can print the values. Not very necessary.
	es := NewEvalState()
	stringParams := ActualStringFormArgsFull("InputForm", es)

	// Test deepcopy
	var t1 = atoms.NewSymbol("System`x")
	t2 := *t1
	t3 := t1.DeepCopy().(*atoms.Symbol)
	assert.Equal(t, "System`x", t1.Name)
	assert.Equal(t, "System`x", t2.Name)
	assert.Equal(t, "System`x", t3.Name)
	t2.Name = "y"
	t3.Name = "z"
	assert.Equal(t, "System`x", t1.Name)
	assert.Equal(t, "y", t2.Name)
	assert.Equal(t, "z", t3.Name)

	var t4 = atoms.NewReal(big.NewFloat(2))
	t5 := *t4
	t6 := t4.DeepCopy().(*atoms.Flt)
	assert.Equal(t, "2.", t4.StringForm(stringParams))
	assert.Equal(t, "2.", t5.StringForm(stringParams))
	assert.Equal(t, "2.", t6.StringForm(stringParams))
	t5.Val.Add(t5.Val, big.NewFloat(2))
	t6.Val.Add(t6.Val, big.NewFloat(3))
	assert.Equal(
		t,
		"4.",
		t4.StringForm(stringParams),
	) // Because we used the wrong copy method
	assert.Equal(t, "4.", t5.StringForm(stringParams))
	assert.Equal(t, "5.", t6.StringForm(stringParams))
}

func TestConcurrency(t *testing.T) {

	fmt.Println("Testing concurrency")

	es1 := NewEvalState()
	es2 := NewEvalState()

	casAssertSame(t, es1, "3", "1+2")
	casAssertSame(t, es2, "3", "1+2")

	var wg sync.WaitGroup

	// Test concurrent evals on different EvalStates.
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(t *testing.T) {
			defer wg.Done()
			esTest := NewEvalState()
			casAssertSame(t, esTest, "3", "1+2")
		}(t)
	}
	wg.Wait()

	// Test read-only concurrent evals on the same EvalState.
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func(t *testing.T, es expreduceapi.EvalStateInterface) {
			defer wg.Done()
			casAssertSame(t, es, "2x", "D[x^2, x]")
		}(t, es1)
	}
	wg.Wait()

	// Test writing concurrent evals on the same EvalState.
	for i := 0; i < 1000; i++ {
		wg.Add(1)
		go func(t *testing.T, i int, es expreduceapi.EvalStateInterface) {
			defer wg.Done()
			EvalInterp(fmt.Sprintf("testVar := %v", i), es)
		}(t, i, es1)
	}
	wg.Wait()

	// Test concurrent MarkSeen.
	for i := 0; i < 1000; i++ {
		wg.Add(1)
		go func(t *testing.T, i int, es expreduceapi.EvalStateInterface) {
			defer wg.Done()
			es.MarkSeen("uniqueIdentifierForMarkSeen")
		}(t, i, es1)
	}
	wg.Wait()
}
