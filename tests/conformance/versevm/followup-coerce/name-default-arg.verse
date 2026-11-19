# followup-coerce (#724): Control of value-default-drop: F2, whose only
# parameter is named and defaulted, named as the argument where a
# type{_():int} is expected. OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints   value 2
F2(?A:int = 2):int = A
Call(F():int):int = F()

Main():void =
    Print("OVPROBE value {Call(F2)}")
