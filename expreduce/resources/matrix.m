Inverse::usage = "`Inverse[mat]` finds the inverse of the square matrix `mat`.";
Inverse[{{a_}}] := {{1/a}};
Inverse[{{a_, b_}, {c_, d_}}] := {{d/(-b c + a d), -(b/(-b c + a d))}, {-(c/(-b c + a d)), a/(-b c + a d)}};
Inverse[{{a_, b_, c_}, {d_, e_, f_}, {h_, i_, j_}}] := {{(-f i + e j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (c i - b j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-c e + b f)/(-c e h + b f h + c d i - a f i - b d j + a e j)}, {(f h - d j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-c h + a j)/(-c e h + b f h + c d i - a f i - b d j + a e j), (c d - a f)/(-c e h + b f h + c d i - a f i - b d j + a e j)}, {(-e h + d i)/(-c e h + b f h + c d i - a f i - b d j + a e j), (b h - a i)/(-c e h + b f h + c d i - a f i - b d j + a e j), (-b d + a e)/(-c e h + b f h + c d i - a f i - b d j + a e j)}};
Attributes[Inverse] = {Protected};
Tests`Inverse = {
    ESimpleExamples[
        ESameTest[{{-2, 1}, {3/2, -(1/2)}}, Inverse[{{1, 2}, {3, 4}}]],
        ESameTest[{{2/5, -(1/5), 0}, {-(1/15), 19/45, -(1/9)}, {-(1/15), -(11/45), 2/9}}, Inverse[{{3, 2, 1}, {1, 4, 2}, {2, 5, 7}}]]
    ], EFurtherExamples[
        EComment["Symbolic elements are handled correctly:"],
        ESameTest[Inverse[{{b}}], {{1/b}}]
    ]
};

Dimensions::usage = "`Dimensions[expr]` finds the dimensions of `expr`.";
Attributes[Dimensions] = {Protected};
Tests`Dimensions = {
    ESimpleExamples[
        ESameTest[{2, 2}, Dimensions[{{1, 3}, {1, 2}}]],
        ESameTest[{2}, Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}}}]]
    ], EFurtherExamples[
        ESameTest[{}, Dimensions[foo]],
        EComment["`Dimensions` works with any head, not just `List`:"],
        ESameTest[{0}, Dimensions[foo[]]]
    ], ETests[
        ESameTest[{2}, Dimensions[{1, 2}]],
        ESameTest[{0}, Dimensions[{}]],
        ESameTest[{1}, Dimensions[foo[{1}]]],
        ESameTest[{1, 1}, Dimensions[{{1}}]],
        ESameTest[{2, 1}, Dimensions[{{1}, {1}}]],
        ESameTest[{2}, Dimensions[{{1}, {1, 2}}]],
        ESameTest[{2, 2}, Dimensions[{{1, 3}, {1, 2}}]],
        ESameTest[{2, 2, 1}, Dimensions[{{{1}, {3}}, {{1}, {2}}}]],
        ESameTest[{2, 2, 2}, Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, {2, 2}}}]],
        ESameTest[{2}, Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}}}]],
        ESameTest[{2, 2, 2}, Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, {foo, 2}}}]],
        ESameTest[{2, 2}, Dimensions[{{{1, 2}, {3, 2}}, {{1, 2}, foo[foo, 2]}}]],
        ESameTest[{1, 2, 0}, Dimensions[{{{}, {}}}]],
        ESameTest[{1, 2}, Dimensions[{{{}, foo[x]}}]]
    ]
};

VectorQ::usage = "`VectorQ[expr]` returns True if `expr` is a vector, False otherwise.";
Attributes[VectorQ] = {Protected};
Tests`VectorQ = {
    ESimpleExamples[
        ESameTest[True, VectorQ[{1, 2, c}]],
        ESameTest[True, VectorQ[{1, 2, foo[a]}]],
        ESameTest[False, VectorQ[foo[1, 2, 3]]],
        ESameTest[False, VectorQ[{1, 2, 3, {}}]],
        ESameTest[True, VectorQ[{f[a], f[b]}]],
        ESameTest[True, VectorQ[{a, c}]],
        ESameTest[True, VectorQ[{}]]
    ]
};

MatrixQ::usage = "`MatrixQ[expr]` returns True if `expr` is a 2D matrix, False otherwise.";
Attributes[MatrixQ] = {Protected};
Tests`MatrixQ = {
    ESimpleExamples[
        ESameTest[False, MatrixQ[{}]],
        ESameTest[True, MatrixQ[{{}}]],
        ESameTest[True, MatrixQ[{{a}}]],
        ESameTest[False, MatrixQ[{{{}}}]],
        ESameTest[False, MatrixQ[{{{a}}}]],
        ESameTest[True, MatrixQ[{{a}, {b}}]],
        ESameTest[True, MatrixQ[{{a, b}, {c, d}}]],
        ESameTest[False, MatrixQ[{{a, b, e}, {c, d}}]],
        ESameTest[True, MatrixQ[{{a, b, e}, {c, d, f}}]],
        ESameTest[False, MatrixQ[{{{a}, {b}}, {{c}, {d}}}]],
        ESameTest[True, MatrixQ[{{a, b, e}}]]
    ]
};

Dot::usage = "`a.b` computes the product of `a` and `b` for vectors and matrices.";
Attributes[Dot] = {Flat, OneIdentity, Protected};
Tests`Dot = {
    ESimpleExamples[
        ESameTest[a c + b d, {a, b}.{c, d}],
        ESameTest[{a, b}.{c, d, e}, {a, b}.{c, d, e}],
        ESameTest[Dot[1, {c, d, e}], Dot[1, {c, d, e}]],
        ESameTest[0, Dot[{}, {}]],
        ESameTest[{{a, b}, {c, d}}.{e, f, g}, {{a, b}, {c, d}}.{e, f, g}],
        ESameTest[{a, b}, Dot[{a, b}]],
        ESameTest[a, Dot[a]],
        ESameTest[1, Dot[1]],
        ESameTest[{{a e + b g, a f + b h}, {c e + d g, c f + d h}}, {{a, b}, {c, d}}.{{e, f}, {g, h}}],
        ESameTest[{{a e + b f}, {c e + d f}}, {{a, b}, {c, d}}.{{e}, {f}}],
        ESameTest[{{a, b}, {c, d}}.{{e, f}}, {{a, b}, {c, d}}.{{e, f}}]
    ], EKnownFailures[
        ESameTest[{a e + b f, c e + d f}, {{a, b}, {c, d}}.{e, f}],
        ESameTest[{a e + c f, b e + d f}, {e, f}.{{a, b}, {c, d}}]
    ]
};

Transpose::usage = "`Transpose[mat]` transposes the first two levels of `mat`";
Attributes[Transpose] = {Protected};
Tests`Transpose = {
    ESimpleExamples[
        ESameTest[Transpose[{a, b}], Transpose[{a, b}]],
        ESameTest[{{a, b}}, Transpose[{{a}, {b}}]],
        ESameTest[{{a}, {b}}, Transpose[{{a, b}}]],
        ESameTest[{{{a}}, {{b}}}, Transpose[{{{a}, {b}}}]],
        ESameTest[Transpose[a], Transpose[a]]
    ]
};
