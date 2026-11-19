# followup-coerce2 (#724): Control of value-return-effect: the parameter
# returned at its own type.
# OpenVerse (Lean and C agreeing) prints value 2
Inc(X:int)<computes>:int = X + 1
Keep(G(:int)<computes>:int):type{_(:int)<computes>:int} = G

Main():void =
    F := Keep(Inc)
    Print("OVPROBE value {F(1)}")
