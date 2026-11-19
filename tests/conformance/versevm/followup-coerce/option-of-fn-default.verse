# followup-coerce (#724): Does UEFN 43.12 admit option{F2} (F2 with a named,
# defaulted parameter) where a ?type{_():int} is expected? OpenVerse admits
# it.
# OpenVerse (Lean and C agreeing) prints   value 2
F2(?A:int = 2):int = A

Main():void =
    O:?type{_():int} = option{F2}
    if (F := O?):
        Print("OVPROBE value {F()}")
