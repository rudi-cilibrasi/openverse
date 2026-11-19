# followup-coerce2 (#724): Control of value-void-result: IntIdentity named
# where a type{_(:int):void} is expected (the Book's Void.versetest:91,
# valid on both VMs). OpenVerse refuses it (the Book survey's
# Void.versetest:92, a gap of its own: a function named at a type whose
# result is void).
# OpenVerse refuses it: expected type{_(:int):void}, found type{_(:int):int}
IntIdentity(X:int):int = X
Run(F(:int):void):void = F(1)

Main():void =
    Run(IntIdentity)
    Print("OVPROBE called")
