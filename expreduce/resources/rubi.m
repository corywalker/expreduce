LoadRubi::usage = "`LoadRubi[]` will load the Rubi integration package by Albert Rich.";
LoadRubi[] := Get["__res__/rubi_loader.m"];
Attributes[LoadRubi] = {Protected};
Tests`LoadRubi = {
    ESimpleExamples[
        ESameTest[Null, LoadRubi[]],
        ESameTest[Log[x], Rubi`Int[1/x, x]],
    ], ETests[
    ]
};
