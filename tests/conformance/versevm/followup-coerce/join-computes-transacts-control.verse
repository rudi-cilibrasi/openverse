# followup-coerce (#724): Control of join-computes-transacts: both branches
# <transacts>, the if's type exactly.
# OpenVerse (Lean and C agreeing) prints true branch 11 | false branch 9
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
Inc(X:int)<transacts>:int = X + 1
Dec(X:int)<transacts>:int = X - 1

Pick(Flag:logic)<transacts>:int =
    F:type{_(:int)<transacts>:int} = if (Flag?) { Inc } else { Dec }
    F(10)

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
