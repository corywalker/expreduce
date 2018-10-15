UnixTime::usage = "`UnixTime[]` returns the integer seconds since the Unix epoch in UTC time.";
Attributes[UnixTime] = {ReadProtected, Protected};
Tests`UnixTime = {
    ESimpleExamples[
        EComment["Get the current Unix timestamp:"],
        EExampleOnlyInstruction["1484805639", "UnixTime[]"],
        EComment["`UnixTime` returns an Integer:"],
        ESameTest[Integer, UnixTime[] // Head]
    ]
};

Pause::usage = "`Pause[d]` sleeps for `d` seconds.";
Attributes[Pause] = {Protected};
Tests`Pause = {
    ESimpleExamples[
        EExampleOnlyInstruction["Null", "Pause[0.001]"],
    ]
};
