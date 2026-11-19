# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a parameter, of type type{_(:int)<computes>:int}) passed
# where a type{_(:int)<transacts>:int} is expected? Epic's 3502 so far is of
# branches of an if and of generic functions; this asks whether every value
# that is not a name needs the wrapper it does not make. OpenVerse's rule
# leaves it admitted (no evidence yet). Control:
# value-computes-as-transacts-control (the parameter already <transacts>).
# OpenVerse (Lean and C agreeing) prints   value 2
Inc(X:int)<computes>:int = X + 1
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<computes>:int)<transacts>:int = Run(G)

Main():void =
    Print("OVPROBE value {Forward(Inc)}")
