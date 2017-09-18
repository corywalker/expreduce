LoadRubi::usage = "`LoadRubi[]` will load the Rubi integration package by Albert Rich.";
LoadRubi[] := Get["__res__/rubi_loader.m"];
Attributes[LoadRubi] = {Protected};
Tests`LoadRubi = {
    ESimpleExamples[
        (*Just test a few cases for a sanity check. Full test suite can be run
        outside of test suite.*)
        ESameTest[Null, LoadRubi[]],
        ESameTest[x^3/3 + 2*x, Rubi`Int[x^2+2, x]],
        ESameTest[Log[x], Rubi`Int[1/x, x]],
    ], ETests[
        ESameTest[x^3/3, Rubi`Int[x^2, x]],
    ]
};
