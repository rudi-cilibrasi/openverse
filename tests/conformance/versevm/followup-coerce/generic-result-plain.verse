# followup-coerce (#724): Control of generic-result-fn: the same parameters,
# the result t (the function type is a parameter's only, as One's).
# OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints took 5 | kept 5
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
TakeInt(X:int):void = Print("OVPROBE took {X}")
Keep(X:t, F(:t):void where t:type):t =
    F(X)
    X

Main():void =
    Print("OVPROBE kept {Keep(5, TakeInt)}")
