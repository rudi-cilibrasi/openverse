# followup-coerce (#724): Does UEFN 43.12 refuse a call of a method of a
# parametric class whose result has the class's type parameter inside a
# function type, on box(int)? OpenVerse's rule covers generic functions
# only: admitted.
# OpenVerse (Lean and C agreeing) prints   took 5
TakeInt(X:int):void = Print("OVPROBE took {X}")
box(t:type) := class:
    Make(F(:t):void):(t->void) = F

Main():void =
    B := box(int){}
    G := B.Make(TakeInt)
    G(5)
