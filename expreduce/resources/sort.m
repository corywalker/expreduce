Sort::usage = "`Sort[list]` sorts the elements in list according to `Order`.";
Attributes[Sort] = {Protected};
Tests`Sort = {
    ESimpleExamples[
        EComment["Sort a list of numbers:"],
        ESameTest[{-5.1, 2, 3.2, 6}, Sort[{6, 2, 3.2, -5.1}]],
        EComment["Sort a list of strings:"],
        ESameTest[{"a", "aa", "hello", "zzz"}, Sort[{"hello", "a", "aa", "zzz"}]],
        EComment["Sort a list of symbols:"],
        ESameTest[{a, b, c, d}, Sort[{d, a, b, c}]],
        EComment["Sort a list of heterogenous expressions:"],
        ESameTest[{5, h, bar[a^x], foo[y, 2]}, Sort[{5, h, foo[y, 2], bar[a^x]}]]
    ], EFurtherExamples[
        EComment["The object to sort need not be a list:"],
        ESameTest[foo[a, b, c, d], Sort[foo[d, a, b, c]]]
    ], ETests[
        ESameTest[{x, 2*x, 2*x^2, y, 2*y, 2*y^2}, Sort[{x, 2*x, y, 2*y, 2*y^2, 2*x^2}]]
    ], EKnownFailures[
        (*Appears to be broken when we switch to the Private` context.*)
        (*Minimal example: Sort[{Private`foo[Private`x]^2,(Private`a+Private`b)^2}]*)
        ESameTest[{1/a,a,a^2,1/b^2,1/b,b,b^2,1/(a+b)^2,a+b,a+b,(a+b)^2,1/foo[x]^2,foo[x],foo[x]^2}, Sort[{a^-1,a,a^2,b^-2,b^-1,b,b^2,(a+b)^-2,(a+b),(a+b)^2,a+b,foo[x],foo[x]^-2,foo[x]^2}]]
    ]
};

Order::usage = "`Order[e1, e2]` returns 1 if `e1` should come before `e2` in canonical ordering, -1 if it should come after, and 0 if the two expressions are equal.";
Attributes[Order] = {Protected};
Tests`Order = {
    ESimpleExamples[
        EComment["Find the relative order of symbols:"],
        ESameTest[1, Order[a, b]],
        ESameTest[-1, Order[b, a]],
        ESameTest[1, Order[a, aa]],
        EComment["Find the relative order of numbers:"],
        ESameTest[-1, Order[2, 1.]],
        ESameTest[1, Order[1, 2]],
        ESameTest[0, Order[1, 1]],
        EComment["Find the relative order of strings:"],
        ESameTest[1, Order["a", "b"]],
        ESameTest[-1, Order["b", "a"]],
        EComment["Find the relative order of heterogenous types:"],
        ESameTest[-1, Order[ab, 1]],
        ESameTest[1, Order[1, ab]],
        ESameTest[-1, Order[y[a], x]],
        EComment["Find the relative order of rationals:"],
        ESameTest[1, Order[Rational[-5, 3], Rational[-4, 6]]],
        ESameTest[-1, Order[Rational[4, 6], .6]],
        ESameTest[1, Order[.6, Rational[4, 6]]],
        ESameTest[1, Order[Rational[4, 6], .7]],
        EComment["Find the relative order of expressions:"],
        ESameTest[0, Order[bar[x, y], bar[x, y]]],
        ESameTest[1, Order[fizz[bar[x, y]], fizz[bar[x, y, a]]]]
    ], ETests[
        (*Symbol ordering*)
        ESameTest[0, Order[a, a]],
        ESameTest[1, Order[a, b]],
        ESameTest[-1, Order[b, a]],
        ESameTest[1, Order[a, aa]],
        ESameTest[1, Order[aa, aab]],
        ESameTest[-1, Order[aab, aa]],
        ESameTest[-1, Order[aa, a]],
        ESameTest[-1, Order[ab, aa]],
        (*Number ordering*)
        ESameTest[-1, Order[2, 1.]],
        ESameTest[1, Order[1, 2]],
        ESameTest[0, Order[1, 1]],
        ESameTest[0, Order[1., 1.]],
        ESameTest[1, Order[1, 1.]],
        ESameTest[-1, Order[1., 1]],
        (*Symbols vs numbers*)
        ESameTest[-1, Order[ab, 1]],
        ESameTest[1, Order[1, ab]],
        (*Sort expressions*)
        ESameTest[-1, Order[foo[x, y], bar[x, y]]],
        ESameTest[1, Order[bar[x, y], foo[x, y]]],
        ESameTest[0, Order[bar[x, y], bar[x, y]]],
        ESameTest[1, Order[bar[x, y], bar[x, y, z]]],
        ESameTest[1, Order[bar[x, y], bar[x, y, a]]],
        ESameTest[1, Order[bar[x, y], bar[y, z]]],
        ESameTest[-1, Order[bar[x, y], bar[w, x]]],
        ESameTest[-1, Order[fizz[foo[x, y]], fizz[bar[x, y]]]],
        ESameTest[1, Order[fizz[bar[x, y]], fizz[foo[x, y]]]],
        ESameTest[0, Order[fizz[bar[x, y]], fizz[bar[x, y]]]],
        ESameTest[1, Order[fizz[bar[x, y]], fizz[bar[x, y, z]]]],
        ESameTest[1, Order[fizz[bar[x, y]], fizz[bar[x, y, a]]]],
        ESameTest[1, Order[fizz[bar[x, y]], fizz[bar[y, z]]]],
        ESameTest[-1, Order[fizz[bar[x, y]], fizz[bar[w, x]]]],
        ESameTest[-1, Order[fizz[foo[x, y]], fizz[bar[a, y]]]],
        ESameTest[-1, Order[fizz[foo[x, y]], fizz[bar[z, y]]]],
        ESameTest[1, Order[1, a[b]]],
        ESameTest[1, Order[1., a[b]]],
        ESameTest[-1, Order[a[b], 1]],
        ESameTest[-1, Order[a[b], 1.]],
        ESameTest[1, Order[x, y[a]]],
        ESameTest[1, Order[x, w[a]]],
        ESameTest[-1, Order[w[a], x]],
        ESameTest[-1, Order[y[a], x]],
        ESameTest[-1, Order[y[], x]],
        ESameTest[-1, Order[y, x]],
        ESameTest[-1, Order[w[], x]],
        ESameTest[1, Order[w, x]],
        (*Test Rational ordering*)
        ESameTest[0, Order[Rational[4, 6], Rational[2, 3]]],
        ESameTest[1, Order[Rational[4, 6], Rational[5, 3]]],
        ESameTest[-1, Order[Rational[5, 3], Rational[4, 6]]],
        ESameTest[1, Order[Rational[-5, 3], Rational[-4, 6]]],
        ESameTest[-1, Order[Rational[4, 6], .6]],
        ESameTest[1, Order[.6, Rational[4, 6]]],
        ESameTest[1, Order[Rational[4, 6], .7]],
        ESameTest[-1, Order[.7, Rational[4, 6]]],
        ESameTest[-1, Order[Rational[4, 6], 0]],
        ESameTest[1, Order[Rational[4, 6], 1]],
        ESameTest[1, Order[0, Rational[4, 6]]],
        ESameTest[-1, Order[1, Rational[4, 6]]],
        ESameTest[1, Order[Rational[4, 6], a]],
        ESameTest[-1, Order[a, Rational[4, 6]]],
        (*Test String ordering*)
        ESameTest[-1, Order["a", 5]],
        ESameTest[-1, Order["a", 5.5]],
        ESameTest[-1, Order["a", 5/2]],
        ESameTest[1, Order["a", x]],
        ESameTest[1, Order["a", x^2]],
        ESameTest[1, Order["a", x^2]],
        ESameTest[-1, Order["b", "a"]],
        ESameTest[1, Order["a", "b"]],
        ESameTest[1, Order["a", "aa"]],
        (*Test polynomial ordering*)
        ESameTest[-1, Order[x^3,4x^2]],
        ESameTest[-1, Order[x^3,4x^2]],
        ESameTest[1, Order[1,4x^2]],
        ESameTest[1, Order[1,4*Sin[x]^2]],
        ESameTest[-1, Order[5x^2,4x^2]],
        ESameTest[-1, Order[4x^3,4x^2]],
        ESameTest[1, Order[x^2,4x^2]],
        ESameTest[1, Order[x^2,foo[x]]],
        ESameTest[1, Order[x^2,x*y]],
        ESameTest[-1, Order[3x^3,4x^2]],
        ESameTest[-1, Order[d*g,d*f]],
        ESameTest[0, Order[d*g,d*g]],
        ESameTest[1, Order[d*g,d*h]],
        ESameTest[1, Order[d*g,e*g]],
        ESameTest[1, Order[d*g,e*h]],
        ESameTest[-1, Order[d g, e f]],
        ESameTest[1, Order[x^2*y,x*y^2]],
        ESameTest[1, Order[x^4*y^2,x^2*y^4]],
        ESameTest[1, Order[x^2*y,2*x*y^2]],
        ESameTest[1, Order[c, 5 * b * c]],
        ESameTest[{-1,-1.,-0.1,0,0.1,0.11,2,2,2.,0.5^x,2^x,x,2 x,x^2,x^x,x^(2 x),xxx,2 y}, Sort[{-1,-1.,0.1,0.11,2.,-.1,2,0,2,2*x,2*y,x,xxx,2^x,x^2,x^x,x^(2*x),.5^x}]],
        ESameTest[-1, Order[foo[x],-x]],
        ESameTest[-1, Order[a[b,piz,foo[]],a[b,foo[]]]],
    ], EKnownFailures[
        ESameTest[{a,A,b,B}, Sort[{a,A,b,B}]],
        ESameTest[{-I,1/A,A,1/k,k}, Sort[{A^(-1), k^(-1), (-I), A, k}]],
        ESameTest[1, Order[a + b - c, a + c]]
    ]
};
