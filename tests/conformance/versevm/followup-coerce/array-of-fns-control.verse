# followup-coerce (#724): Control of array-of-fns-default: functions of
# type{_():int} exactly.
# OpenVerse (Lean and C agreeing) prints value 2 | value 4
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
G2():int = 2
G4():int = 4

Main():void =
    Fs:[]type{_():int} = array{G2, G4}
    for (F : Fs):
        Print("OVPROBE value {F()}")
