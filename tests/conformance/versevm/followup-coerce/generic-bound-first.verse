# followup-coerce (#724): Control of generic-arg-concrete: Identity bound to
# a local of type type{_(:int):int} first, the local passed. OpenVerse
# admits it.
# OpenVerse (Lean and C agreeing) prints value 1
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
Identity(X:t where t:type):t = X
ApplyInt(F(:int):int, X:int):int = F(X)

Main():void =
    F:type{_(:int):int} = Identity
    Print("OVPROBE value {ApplyInt(F, 1)}")
