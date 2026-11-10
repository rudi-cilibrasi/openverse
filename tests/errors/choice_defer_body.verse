# expect: 4:37: a choice (a | b) has several values, so it must be in a failure context
# (a defer:'s body is no failure context, also in a block lifted for its choice, #283)
Main()<transacts>:void =
    for (V := block{ defer: { X := 1 | 2; Print("d {X}") }; Y := 1 | 2; Y }) { Print("v {V}") }
