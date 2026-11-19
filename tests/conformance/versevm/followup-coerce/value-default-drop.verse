# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a local bound to F2, of type (?A:int = ...)->int) passed
# where a type{_():int} is expected? (The name gets the wrapper:
# join-named-default-fn-control, name-default-arg.) OpenVerse's rule left it
# admitted until Epic answered.
# OpenVerse refuses it: 3502 rule: using a value of type type{_(?A:int =
# …):int} as a value of type type{_():int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L12 "Using a value of type (?A:int = ...)->int as a value
# of type tuple()->int is not yet implemented."
F2(?A:int = 2):int = A
Call(F():int):int = F()

Main():void =
    G := F2
    Print("OVPROBE value {Call(G)}")
