# Expreduce
[![Build Status](https://travis-ci.org/corywalker/expreduce.svg?branch=master)](https://travis-ci.org/corywalker/expreduce)

This software is experimental quality and is not currently intended for serious use. There are plenty of more mature open source computer algebra systems to use instead.

Expreduce is a language with specialized constructs for term rewriting. It is a neat language for a computer algebra system because it is able to express expression manipulation steps in a form very similar to standard math equations. For example, the product rule in calculus can be expressed as:

```
D[a_*b__,x_] := D[a,x]*b + a*D[Times[b],x]
```

The term rewriting system and pattern matching engine is fairly advanced. The computer algebra system at this stage is extremely limited, but fairly simple calculus and algebraic manipulation is certainly supported (see examples below). If you are looking for a more mature computer algebra system, please consider using Mathematica (proprietary) or Mathics (open source, Sympy-backed).

## Documentation

Expreduce has documentation for every function that is supported. [Link to documentation](https://corywalker.github.io/expreduce-docs/).

# Setup
`go generate` is required to generate source files from lex and yacc:
```
go get -d ./...
go get golang.org/x/tools/cmd/goyacc
go get github.com/cznic/golex
go generate ./...
go get ./...
```

# Example
This must be done after running "go generate". To run the example CAS prompt:

```
cd example
go run calc.go
```

```
# go run calc.go

Welcome to Expreduce!

In[1]:= D[Sin[x]/x,x]

Out[1]= ((-1 * x^-2 * Sin[x]) + (Cos[x] * x^-1))

In[2]:= Table[a^2,{a,1,10}]

Out[2]= {1, 4, 9, 16, 25, 36, 49, 64, 81, 100}

In[3]:= Sum[i, {i, 1, n}]

Out[3]= (1/2 * (1 + n) * n)

In[4]:= (2^(-1) * n * (1 + n)) /. n->5

Out[4]= 15

In[5]:= Total[Table[i,{i,1,5}]]

Out[5]= 15

In[6]:= bar[1, foo[a, b]] + bar[2, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] + bar[bmatch_Integer, foo[cmatch__]] -> bar[amatch + bmatch, foo[cmatch]]

Out[6]= bar[3, foo[a, b]]
```

# Other projects

Expreduce is indeed very similar to Mathics, a similar term rewriting system that uses Sympy as a backend for CAS operations. I created expreduce for a few reasons. The first is that I wanted to learn everything I could about term rewriting systems. The second is that I believe the syntax implemented in here is better suited for building a computer algebra system than using Python to manipulate expressions (as Sympy, and thus Mathics does). Using a language with first-class support for pattern matching and replacement across expression trees is ideal for writing a computer algebra system. This combined with an optimized core can lead to efficient and informed evaluation without much translation work for the programmer when translating equations to code.

# Current limitations

When the engine applies rules for a given symbol, it tries to match the most "specific" rules first. The current definition of specificity is fairly basic now, but can certainly be improved upon. It works in most cases but I can envision cases where it will be wrong. Right now there is no way to override the order of rule application, but it should be fairly simple to add in the future.

The pattern matching system can be very slow, especially when working with `Orderless` expressions with many terms. This is because correctly matching such terms often involves checking many different permutations of a pattern until one finds a match. My theory right now is that the current matching system is behaving naively and that it can be modified to speed things up.

# Development

To run the tests:
```
cd expreduce
go test
```
