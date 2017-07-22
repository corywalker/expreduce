RandomReal::usage = "`RandomReal[]` generates a random floating point from 0 to 1.

`RandomReal[max]` generates a random floating point from 0 to `max`.

`RandomReal[min, max]` generates a random floating point from `min` to `max.";
RandomReal[{min_, max_}] := RandomReal[]*(max - min) + min;
RandomReal[max_] := RandomReal[]*max;
Attributes[RandomReal] = {Protected};
Tests`RandomReal = {
    ESimpleExamples[
        EExampleOnlyInstruction["0.0750914", "RandomReal[]"]
    ], EFurtherExamples[
        EComment["Use `SeedRandom` to seed the RNG:"],
        EExampleOnlyInstruction["Null", "SeedRandom[3]"],
        EExampleOnlyInstruction["0.719983", "RandomReal[]"],
        EExampleOnlyInstruction["0.652631", "RandomReal[]"],
        EExampleOnlyInstruction["Null", "SeedRandom[3]"],
        EExampleOnlyInstruction["0.719983", "RandomReal[]"]
    ]
};

SeedRandom::usage = "`SeedRandom[seed]` seeds the internal random number generator with a given integer `seed`.";
Attributes[SeedRandom] = {Protected};
Tests`SeedRandom = {
    ESimpleExamples[
        EExampleOnlyInstruction["0.0750914", "RandomReal[]"],
        EExampleOnlyInstruction["Null", "SeedRandom[3]"],
        EExampleOnlyInstruction["0.719983", "RandomReal[]"],
        EExampleOnlyInstruction["0.652631", "RandomReal[]"],
        EExampleOnlyInstruction["Null", "SeedRandom[3]"],
        EExampleOnlyInstruction["0.719983", "RandomReal[]"]
    ]
};
