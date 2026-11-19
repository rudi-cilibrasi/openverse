# followup-coerce (#724): Control of value-computes-as-transacts: the
# parameter passed on at its own type (Inc named as a <transacts> value, the
# wrapper a name gets).
# OpenVerse (Lean and C agreeing) prints   value 2
Inc(X:int)<computes>:int = X + 1
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<transacts>:int)<transacts>:int = Run(G)

Main():void =
    Print("OVPROBE value {Forward(Inc)}")
