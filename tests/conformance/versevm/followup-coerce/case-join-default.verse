# followup-coerce (#724): Does UEFN 43.12 refuse a case whose arms are F2
# and F4 (named, defaulted parameters) at type{_():int}, as it refuses an
# if's branches (join-named-default-fn)? OpenVerse's rule covers if only:
# admitted. Control: case-join-control.
# OpenVerse (Lean and C agreeing) prints one 2 | two 4
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B

Pick(N:int):int =
    F:type{_():int} = case (N):
        1 => F2
        _ => F4
    F()

Main():void =
    Print("OVPROBE one {Pick(1)}")
    Print("OVPROBE two {Pick(2)}")
