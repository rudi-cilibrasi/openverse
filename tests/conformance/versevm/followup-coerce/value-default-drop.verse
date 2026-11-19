# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a local bound to F2, of type (?A:int = ...)->int) passed
# where a type{_():int} is expected? (The name gets the wrapper:
# join-named-default-fn-control, name-default-arg.) OpenVerse's rule leaves
# it admitted.
# OpenVerse (Lean and C agreeing) prints   value 2
F2(?A:int = 2):int = A
Call(F():int):int = F()

Main():void =
    G := F2
    Print("OVPROBE value {Call(G)}")
