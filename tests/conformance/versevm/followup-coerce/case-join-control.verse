# followup-coerce (#724): Control of case-join-default: arms of
# type{_():int} exactly.
# OpenVerse (Lean and C agreeing) prints one 2 | two 4
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
G2():int = 2
G4():int = 4

Pick(N:int):int =
    F:type{_():int} = case (N):
        1 => G2
        _ => G4
    F()

Main():void =
    Print("OVPROBE one {Pick(1)}")
    Print("OVPROBE two {Pick(2)}")
