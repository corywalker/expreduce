AppendTo[list_, e_] := (list = Append[list, e]);

Attributes[AppendTo] = {HoldFirst, Protected};

PrependTo[list_, e_] := (list = Prepend[list, e]);

Attributes[PrependTo] = {HoldFirst, Protected};
