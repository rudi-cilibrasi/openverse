# followup-coerce (#724): Does UEFN 43.12 admit option{F2} (F2 with a named,
# defaulted parameter) where a ?type{_():int} is expected? OpenVerse
# admitted it until Epic answered.
# OpenVerse refuses it: 3502 rule: using a value of type ?type{_(?A:int =
# …):int} as a value of type ?type{_():int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L8 "Using a value of type ?((?A:int = ...)->int) as a
# value of type ?(tuple()->int) is not yet implemented."
F2(?A:int = 2):int = A

Main():void =
    O:?type{_():int} = option{F2}
    if (F := O?):
        Print("OVPROBE value {F()}")
