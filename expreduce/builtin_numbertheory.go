package expreduce

import (
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/kavehmz/prime"
)

// Compute the prime factors of a positive n.
// TODO: use Pollard's rho algorithm and potentially have an int64 version.
func primeFactors(origN *big.Int) (factors []*big.Int) {
	zero := big.NewInt(0)
	one := big.NewInt(1)
	if origN.Cmp(one) == 0 {
		factors = append(factors, big.NewInt(1))
		return
	}
	i := big.NewInt(2)
	modRes := big.NewInt(0)
	n := big.NewInt(0)
	n.Set(origN)
	for n.Cmp(one) != 0 {
		for (modRes.Mod(n, i)).Cmp(zero) != 0 {
			i.Add(i, one)
		}
		newFactor := big.NewInt(0)
		newFactor.Set(i)
		factors = append(factors, newFactor)
		n.Div(n, i)
		i.SetInt64(2)
	}
	return
}

type factorTally struct {
	factor *big.Int
	power  uint64
}

func primeFactorsTallied(n *big.Int) (factorTallies []factorTally) {
	factors := primeFactors(n)
	for _, factor := range factors {
		added := false
		for i := range factorTallies {
			if factorTallies[i].factor.Cmp(factor) == 0 {
				factorTallies[i].power++
				added = true
				break
			}
		}
		if !added {
			factorTallies = append(factorTallies, factorTally{
				factor: factor,
				power:  1,
			})
		}
	}
	return
}

func getNumberTheoryDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:         "PrimeQ",
		legacyEvalFn: singleParamQEval(primeQ),
	})
	defs = append(defs, Definition{
		Name: "GCD",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			zero := big.NewInt(0)
			var ints [](*big.Int)
			for i := 1; i < len(this.GetParts()); i++ {
				asInt, isInt := this.GetParts()[i].(*atoms.Integer)
				if !isInt {
					return this
				}
				r := asInt.Val.Cmp(zero)
				if r > 0 {
					tmpI := big.NewInt(0)
					tmpI.Set(asInt.Val)
					ints = append(ints, tmpI)
				}
				if r < 0 {
					tmpI := big.NewInt(0)
					tmpI.Neg(asInt.Val)
					ints = append(ints, tmpI)
				}
			}
			if len(ints) == 0 {
				return atoms.NewInteger(zero)
			}
			gcd := ints[0]
			for i := 1; i < len(ints); i++ {
				gcd.GCD(nil, nil, gcd, ints[i])
			}
			return atoms.NewInteger(gcd)
		},
	})
	defs = append(defs, Definition{Name: "LCM"})
	defs = append(defs, Definition{
		Name: "Mod",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			xi, xIsInt := this.GetParts()[1].(*atoms.Integer)
			yi, yIsInt := this.GetParts()[2].(*atoms.Integer)
			if !xIsInt || !yIsInt {
				return this
			}
			if yi.Val.Cmp(big.NewInt(0)) == 0 {
				return atoms.NewSymbol("System`Indeterminate")
			}
			m := big.NewInt(0)
			m.Mod(xi.Val, yi.Val)
			return atoms.NewInteger(m)
		},
	})
	defs = append(defs, Definition{
		Name:       "PrimePi",
		Usage:      "`PrimePi[n]` returns the number of primes less than or equal to `n`.",
		Attributes: []string{"Listable"},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			n := int64(0)
			asInt, isInt := this.GetParts()[1].(*atoms.Integer)
			if isInt {
				n = asInt.Val.Int64()
			}
			asFlt, isFlt := this.GetParts()[1].(*atoms.Flt)
			if isFlt {
				n, _ = asFlt.Val.Int64()
			}
			if !isInt && !isFlt {
				return this
			}
			if n <= 0 {
				return atoms.NewInteger(big.NewInt(0))
			}
			if n == 1 {
				return atoms.NewInteger(big.NewInt(1))
			}
			// A very inefficient implementation
			p := prime.Primes(uint64(n))
			return atoms.NewInteger(big.NewInt(int64(len(p))))
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"4", "PrimePi[7]"},
			&SameTest{"78498", "PrimePi[10^6]"},
			&SameTest{"0", "PrimePi[-5]"},
		},
		Tests: []TestInstruction{
			&SameTest{"0", "PrimePi[0]"},
			&SameTest{"4", "PrimePi[8]"},
			&SameTest{"PrimePi[a]", "PrimePi[a]"},
			&SameTest{"1", "PrimePi[1]"},
			&SameTest{"1", "PrimePi[2]"},
			&SameTest{"3", "PrimePi[6]"},
			&SameTest{"4", "PrimePi[7.]"},
			&SameTest{"3", "PrimePi[6.9]"},
			&SameTest{"3", "PrimePi[6.9]"},
		},
	})
	/*defs = append(defs, Definition{
		Name: "Prime",
		Usage: "`Prime[n]` returns the `n`th prime number.",
		Attributes: []string{"Listable"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			asInt, isInt := this.Parts[1].(*Integer)
			if !isInt {
				return this
			}
			n := asInt.Val.Int64()
			if n <= 0 {
				return this
			}
			p := prime.Primes(uint64(n))
			//return &Integer{big.NewInt(0)}
			// A hack to get this working would be to find an upper bound on
			// the PrimePi funciton given an n value, and use that as the input
			// to the Primes() function. Then I can directly select the nth
			// value from the slice. See:
			// https://math.stackexchange.com/questions/479798/estimating-the-upper-bound-of-prime-count-in-the-given-range
			return &Integer{big.NewInt(int64(p[len(p)-1]))}
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"5", "Prime[3]"},
			&SameTest{"27449", "Prime[3000]"},
		},
		Tests: []TestInstruction{
			&SameTest{"Prime[0]", "Prime[0]"},
			&SameTest{"Prime[1.]", "Prime[1.]"},
			&SameTest{"2", "Prime[1]"},
		},
	})*/
	defs = append(defs, Definition{Name: "EvenQ"})
	defs = append(defs, Definition{Name: "OddQ"})
	defs = append(defs, Definition{Name: "FactorInteger"})
	defs = append(defs, Definition{Name: "FractionalPart"})
	defs = append(defs, Definition{Name: "IntegerPart"})
	defs = append(defs, Definition{Name: "PowerMod"})
	defs = append(defs, Definition{Name: "EulerPhi"})
	defs = append(defs, Definition{Name: "Fibonacci"})
	defs = append(defs, Definition{Name: "IntegerDigits"})
	defs = append(defs, Definition{Name: "FromDigits"})
	defs = append(defs, Definition{Name: "Sign"})
	return
}
