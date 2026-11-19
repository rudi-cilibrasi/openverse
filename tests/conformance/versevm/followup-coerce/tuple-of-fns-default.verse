# followup-coerce (#724): Does UEFN 43.12 admit a tuple holding F2 (a named,
# defaulted parameter) where a tuple(type{_():int}, int) is expected?
# OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints   value 2
F2(?A:int = 2):int = A

Main():void =
    T:tuple(type{_():int}, int) = (F2, 1)
    Print("OVPROBE value {T(0)()}")
