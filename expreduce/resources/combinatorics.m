IntegerPartitions::usage = "`IntegerPartitions[n]` lists the possible ways to partition `n` into smaller integers.

`IntegerPartitions[n, k]` lists the possible ways to partition `n` into smaller integers, using up to `k` elements.";
Attributes[IntegerPartitions] = {Protected};
Tests`IntegerPartitions = {
    ESimpleExamples[
        EComment["Find the partitions of 4:"],
        ESameTest[{{4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1}}, IntegerPartitions[4]],
        EComment["Find the partitions of 10, using a maximum of k = 2 integers:"],
        ESameTest[{{10}, {9, 1}, {8, 2}, {7, 3}, {6, 4}, {5, 5}}, IntegerPartitions[10, 2]]
    ], EFurtherExamples[
        EComment["The partitions of zero is a nested empty List:"],
        ESameTest[{{}}, IntegerPartitions[0]]
    ], ETests[
        ESameTest[{{1}}, IntegerPartitions[1]],
        ESameTest[{}, IntegerPartitions[-1]],
        ESameTest[{}, IntegerPartitions[-5]],
        ESameTest[IntegerPartitions[.5], IntegerPartitions[.5]],
        ESameTest[{{10}}, IntegerPartitions[10, 1]],
        ESameTest[{}, IntegerPartitions[10, 0]]
    ]
};

Permutations::usage = "`Permutations[list]` lists the possible permutations for a given list.";
Attributes[Permutations] = {Protected};
Tests`Permutations = {
    ESimpleExamples[
        EComment["Find the permutations of `{1, 2, 3}`:"],
        ESameTest[{{1, 2, 3}, {1, 3, 2}, {2, 1, 3}, {2, 3, 1}, {3, 1, 2}, {3, 2, 1}}, Permutations[Range[3]]],
        EComment["`Permutations` ignores duplicates:"],
        ESameTest[{{1, 2, 2}, {2, 1, 2}, {2, 2, 1}}, Permutations[{1, 2, 2}]]
    ]
};

Multinomial::usage = "`Multinomial[n1, n2, ...]` gives the multinomial coefficient for the given term.";
Multinomial[seq___] := Factorial[Apply[Plus, {seq}]] / Apply[Times, Map[Factorial, {seq}]];
Attributes[Multinomial] = {Listable, NumericFunction, Orderless, ReadProtected, Protected};
Tests`Multinomial = {
    ESimpleExamples[
        EComment["Find the multinomial coefficient for the 1, 3, 1 term:"],
        ESameTest[20, Multinomial[1, 3, 1]],
        EComment["`Multinomial` handles symbolic arguments:"],
        ESameTest[Factorial[k+2] / Factorial[k], Multinomial[1,k,1]]
    ]
};

Factorial::usage = "`n!` returns the factorial of `n`.";
Attributes[Factorial] = {Listable, NumericFunction, ReadProtected, Protected};
Tests`Factorial = {
    ESimpleExamples[
        ESameTest[2432902008176640000, 20!],
        ESameTest[120, Factorial[5]]
    ], EFurtherExamples[
        ESameTest[1, Factorial[0]],
        ESameTest[ComplexInfinity, Factorial[-1]]
    ], ETests[
        ESameTest[1, Factorial[1]],
        ESameTest[1, Factorial[0]],
        ESameTest[1, Factorial[-0]],
        ESameTest[ComplexInfinity, Factorial[-10]],
        ESameTest[120, Factorial[5]],
        ESameTest[Indeterminate, 0 * Infinity],
        ESameTest[Indeterminate, 0 * ComplexInfinity]
    ]
};

Tuples::usage = "`Tuples[list, n]` all possible tuples of `list` of length `n`.";
(* Base case: n = 0, return an empty list *)
Tuples[_, 0] := {{}}
(* Recursive case *)
Tuples[list_, n_Integer?Positive] :=
  Module[{prevTuples, newTuples},
    prevTuples = Tuples[list, n - 1];
    newTuples = Flatten[
      Table[
        Prepend[#, elem] & /@ prevTuples,
        {elem, list}
      ],
      1
    ];
    newTuples
  ]
Attributes[Tuples] = {Protected};
Tests`Tuples = {
    ESimpleExamples[
        ESameTest[{{1,1},{1,2},{1,3},{2,1},{2,2},{2,3},{3,1},{3,2},{3,3}}, Tuples[Range[1, 3], 2]]
    ]
};