# followup-coerce2 (#724): Does UEFN 43.12 admit an object's <computes>
# method passed to a generic function whose parameter is a <transacts>
# function of its type parameters (Apply(C.Inc, 1); the Book's
# ParametricFunctions.versetest:189 passes a function, valid)? OpenVerse
# admits it: the method is named at the parameter's type once the call gives
# it.
# OpenVerse (Lean and C agreeing) prints value 2
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19) admits
# it.
counter := class:
    Inc(X:int)<computes>:int = X + 1
Apply(F(:t)<transacts>:u, X:t where t:type, u:type):u = F(X)

Main():void =
    C := counter{}
    Print("OVPROBE value {Apply(C.Inc, 1)}")
