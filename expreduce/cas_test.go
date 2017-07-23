package expreduce

import (
	"flag"
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"regexp"
	"testing"
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

	// Test basic float functionality
	var f *Flt = &Flt{big.NewFloat(5.5)}
	assert.Equal(t, "5.5", f.String())
	f.Eval(es)
	assert.Equal(t, "5.5", f.String())

	// Test nested addition functionality
	var a = NewExpression([]Ex{
		&Symbol{"System`Plus"},
		NewExpression([]Ex{
			&Symbol{"System`Plus"},
			&Flt{big.NewFloat(80)},
			&Flt{big.NewFloat(3)},
		}),

		&Flt{big.NewFloat(2)},
		&Flt{big.NewFloat(2.5)},
	})

	// Test equality checking
	assert.Equal(t, "EQUAL_TRUE", (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(99)}, &es.CASLogger))
	assert.Equal(t, "EQUAL_FALSE", (&Flt{big.NewFloat(99)}).IsEqual(&Flt{big.NewFloat(98)}, &es.CASLogger))
	assert.Equal(t, "EQUAL_TRUE", (&Symbol{"System`x"}).IsEqual(&Symbol{"System`x"}, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", (&Symbol{"System`x"}).IsEqual(&Symbol{"System`X"}, &es.CASLogger))
	assert.Equal(t, "EQUAL_UNK", (&Symbol{"System`x"}).IsEqual(&Symbol{"System`y"}, &es.CASLogger))

	// Test evaluation
	newa := a.Eval(es)
	assert.Equal(t, "87.5", newa.String())

	// Test basic Symbol functionality
	var v *Symbol = &Symbol{"System`x"}
	assert.Equal(t, "x", v.String())
	v.Eval(es)
	assert.Equal(t, "x", v.String())

	assert.Equal(t, "(a + b + c + d + e + f)", EasyRun("a + b + c +d +e +f", es))
	assert.Equal(t, "(a * b * c * d * e * f)", EasyRun("a * b * c *d *e *f", es))

	CasAssertSame(t, es, "2", "iubjndxuier = 2")
	_, containsTest := es.defined["Global`iubjndxuier"]
	assert.True(t, containsTest)
	es.ClearAll()
	_, containsTest = es.defined["Global`iubjndxuier"]
	assert.False(t, containsTest)
}

func TestDeepCopy(t *testing.T) {
	fmt.Println("Testing deepcopy")

	// Test deepcopy
	var t1 = &Symbol{"System`x"}
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

	var t4 = &Flt{big.NewFloat(2)}
	t5 := *t4
	t6 := t4.DeepCopy().(*Flt)
	assert.Equal(t, "2.", t4.String())
	assert.Equal(t, "2.", t5.String())
	assert.Equal(t, "2.", t6.String())
	t5.Val.Add(t5.Val, big.NewFloat(2))
	t6.Val.Add(t6.Val, big.NewFloat(3))
	assert.Equal(t, "4.", t4.String()) // Because we used the wrong copy method
	assert.Equal(t, "4.", t5.String())
	assert.Equal(t, "5.", t6.String())
}
