# followup-coerce (#724): Control of join-method-values: both methods
# <transacts>.
# OpenVerse (Lean and C agreeing) prints   true branch 11 | false branch 9
counter := class:
    Inc(X:int)<transacts>:int = X + 1
    Dec(X:int)<transacts>:int = X - 1

Pick(C:counter, Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { C.Inc } else { C.Dec }
    F(10)

Main():void =
    C := counter{}
    Print("OVPROBE true branch {Pick(C, true)}")
    Print("OVPROBE false branch {Pick(C, false)}")
