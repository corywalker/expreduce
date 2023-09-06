# Expreduce
[![Go](https://github.com/corywalker/expreduce/actions/workflows/go.yml/badge.svg)](https://github.com/corywalker/expreduce/actions/workflows/go.yml)

This software is experimental quality and is not currently intended for serious use. There are plenty of more mature open source computer algebra systems to use instead.

Expreduce implements a language with specialized constructs for term rewriting. It is a neat language for a computer algebra system because it is able to express expression manipulation steps in a form very similar to standard math equations. For example, the product rule in calculus can be expressed as:

```
D[a_*b_,x_] := D[a,x]*b + a*D[b,x]
```

Now that the kernel understands the product rule, when it later encounters a pattern matching the above LHS, it will recursively apply the product rule until the expression stabilizes.

The term rewriting system and pattern matching engine is fairly advanced. The computer algebra system at this stage is extremely limited, but simple calculus and algebraic manipulation is certainly supported (see examples below). If you are looking for a more mature computer algebra system, please consider using Mathematica (proprietary) or Mathics (open source, Sympy-backed).

![Jupyter screenshot](/images/jupyter_screenshot.png)

This screenshot demonstrates the Jupyter notebook interface for Expreduce. This Jupyter extension can be found [here](https://github.com/mmatera/iwolfram).

# Install and run

[DOWNLOAD HERE](https://github.com/corywalker/expreduce/releases/latest)

If you just want to get started, you can download a binary release and run the software without any downloading Go or compiling. Head over to the [latest release](https://github.com/corywalker/expreduce/releases/latest) and download the correct package for your OS/architecture.

## From source

```
$ go get github.com/corywalker/expreduce
$ expreduce
```

## Documentation

Expreduce has documentation for every function that is supported. [Link to documentation](https://corywalker.github.io/expreduce-docs/).

# Example
```
Welcome to Expreduce!

In[1]:= D[Cos[Log[Sin[x]]+x]+x,x]

Out[1]= 1 + -(1 + Cot[x])*Sin[x + Log[Sin[x]]]

In[2]:= Integrate[5*E^(3*x),{x,2,a}] // Expand

Out[2]= -5/3*E^6 + 5/3*E^(3*a)

In[3]:= FactorSquareFree[1 - 2*x^2 + x^4]

Out[3]= (-1 + x^2)^2

In[4]:= Sum[i, {i, 1, n}]

Out[4]= 1/2*n*(1 + n)

In[5]:= Together[(1/2 + 3/a)^2+b/c]

Out[5]= 1/4*a^-2*c^-1*(4*a^2*b + 36*c + 12*a*c + a^2*c)

In[6]:= 40!

Out[6]= 815915283247897734345611269596115894272000000000

In[7]:= Solve[x^2-x-2.5==0,x]

Out[7]= {{x -> -1.15831}, {x -> 2.15831}}
```

# Rubi integration rules

Expreduce uses the Rubi integration suite by Albert Rich. The rules can be loaded by running `LoadRubi[]` and then the integration can be called like `Int[Sin[a + b*Log[c*x^n]], x]`. These rules are much more powerful than the simplistic ones in `Integrate[]`.

http://www.apmaths.uwo.ca/~arich/

## Integration examples

```
In[1]:= Int[((A + C*Sin[e + f*x]^2)*(a + a*Sin[e + f*x])^m*(c + -c*Sin[e + f*x])^(-1/2)), x]

Out[1]= (f^-1*Cos[e + f*x]*Hypergeometric2F1[1, 1/2 + m, 3/2 + m, 1/2*(1 + Sin[e + f*x])]*(1 + 2*m)^-1*(A + C)*(a + a*Sin[e + f*x])^m*(c + -c*Sin[e + f*x])^(-1/2) + -2*C*a^-1*f^-1*Cos[e + f*x]*(3 + 2*m)^-1*(a + a*Sin[e + f*x])^(1 + m)*(c + -c*Sin[e + f*x])^(-1/2))

In[2]:= Int[(x^-5*(a*x)^(-1/2)*(1 + -a*x)^(-1/2)*(1 + a*x)), x]

Out[1]= (-2/9*a^4*(a*x)^(-9/2)*(1 + -a*x)^(1/2) + -34/63*a^4*(a*x)^(-7/2)*(1 + -a*x)^(1/2) + -68/105*a^4*(a*x)^(-5/2)*(1 + -a*x)^(1/2) + -272/315*a^4*(a*x)^(-3/2)*(1 + -a*x)^(1/2) + -544/315*a^4*(a*x)^(-1/2)*(1 + -a*x)^(1/2))
```

# Technical notes

In Expreduce, everything is an expression, which can either be an atomic value like an Integer or a Symbol, or it can be an ordered list of subexpressions. In the case of an ordered list of subexpressions, the first element is known as the Head. It specifies what kind of data follows. For example, `a + 1` is represented as `Plus[a, 1]`. Here the head is `Plus` and the two subexpressions that follow are the symbol `a` and the integer `1`.

When the interpreter encounters an expression that it has not yet evaluated, it checks for a match with the internal database of rules. The internal rule collection is keyed on the head of the expression. An example would be `Cos[n_Integer?EvenQ*Pi] := 1`, which means that taking the cosine of an even multiple of pi should evaluate to 1.

The pattern matching must be fast for efficient evaluation. Internally, all expressions maintain a corresponding [Merkle tree](https://en.wikipedia.org/wiki/Merkle_tree). Each expression and subexpression will often know the hash of its contents without any computation. This makes checking for expression sameness as simple as checking for the equality of two int64 values. When there are patterns in the RHS of the match, we can no longer rely only on the hash, but Expreduce has a mostly efficient match iterator that checks for any possible matches.

It's important to note that an expression can match a pattern in multiple ways. A simple example is `MatchQ[x + y, a_ + b_]`. Here, a could hold x and b could hold y or a could hold y and b could hold x. The match iterator iterates over all possible allocations (how many expressions a pattern will match with). The match iterator will also iterate over all possible assignments for each allocation. An assignment specifies which subexpressions would match to a pattern, not just how many.

# Other projects

Expreduce is indeed very similar to Mathics, a similar term rewriting system that uses Sympy as a backend for CAS operations. I created expreduce for a few reasons. The first is that I wanted to learn everything I could about term rewriting systems. The second is that I believe the syntax implemented in here is better suited for building a computer algebra system than using Python to manipulate expressions (as Sympy, and thus Mathics does). Using a language with first-class support for pattern matching and replacement across expression trees is ideal for writing a computer algebra system. This combined with an optimized core can lead to efficient and informed evaluation without much translation work for the programmer when translating equations to code.

# Current limitations

When the engine applies rules for a given symbol, it tries to match the most "specific" rules first. The current definition of specificity is basic now, but can certainly be improved upon. It works in most cases but I can envision cases where it will be wrong. Right now there is no way to override the order of rule application, but it should be simple to add in the future.

The pattern matching system can be very slow, especially when working with `Orderless` expressions with many terms. This is because correctly matching such terms often involves checking many different permutations of a pattern until one finds a match. My theory right now is that the current matching system is behaving naively and that it can be modified to speed things up.

# Future directions

I'm interested in trying to apply Golang's concurrency paradigms to the evaluation sequence. Some low hanging fruit would be to have parallel computation of mapping pure functions onto Lists or other expressions (computing the derivative of a list expressions). Similarly, supporting automatic threading of Listable functions would be nice (computing sin(x) of a large array). The evaluation of an expression often starts with evaluating each of the parameters at the beginning. This could potentially be made concurrent as well. A more complicated but very interesting application would be to break down the pattern matching engine into concurrent components. We would have to be very careful about side effects here, so we might need to overhaul our scoping constructs or somehow restrict access to the EvalState. Another option would be to create a function that predicts if another function has side effects (is this feasible?). A true prediction could allow the system to fall back to non-concurrent evaluation.

Since there are at least two other replacement engines that implement the same syntax that I know of ([another one here](https://github.com/jyh1/mmaclone)), it would could be useful to decide on a standard link protocol such that the replacement engine is independent of the rules that run on top of it. Another layer of abstraction is the frontend. Really the hierarchy goes as follows: core <- rules <- frontend. It would be nice to see all of these functions factored out and interchangeable.

Also of interest is to build up some formal theory on the rule definitions. There should be some pre-existing literature on this, as term-rewriting is a studied field. Some interesting questions to answer are:

1. Given a set of rules for a symbol (or the universe of rules?), can we find duplicates or reduce the set of rules to the most fundamental ones? Answering such a question would improve the efficiency and clarity of the system.
2. Given a set of rules for a symbol (or the universe of rules?), can we prove that the recursive rewrites will terminate? It is fairly easy to write a rule that loops on itself or in cooperation with other rules. Of course, we should remove from consideration some of the imperative symbols such as `While` and `For`. Even with these imperative functions removed, is this question still the halting problem? Can we restrict our considerations enough such that the problem is not the halting problem? Answering this question would improve the stability of the system.

# Development

Pretty standard Go workflow. Just remember to `go generate`.

```
# To update any .m changes or changes to the parser:
go generate ./...
# To run the test suite:
go test ./...
# Or to test some important parts with helpful information printed:
go test -v github.com/corywalker/expreduce/expreduce -count=1
# To exit early, press Ctrl-\
# To quickly iterate on one module:
go generate ./expreduce/builtin.go && go test -v github.com/corywalker/expreduce/expreduce -count=1 -testmodules=combinatorics -run=TestIncludedModules
```

The use of `go generate` might require the download of additional dependencies, for example `go install github.com/go-bindata/go-bindata/...@latest`.
