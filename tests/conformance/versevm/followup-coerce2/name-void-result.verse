# followup-coerce2 (#724): Control of value-void-result: IntIdentity named
# where a type{_(:int):void} is expected (the Book's Void.versetest:91,
# valid on both VMs). OpenVerse refused it until Epic answered (the Book
# survey's Void.versetest:92: a function named at a type whose result is
# void).
# OpenVerse (Lean and C agreeing) prints called
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19) admits
# it.
IntIdentity(X:int):int = X
Run(F(:int):void):void = F(1)

Main():void =
    Run(IntIdentity)
    Print("OVPROBE called")
