# followup-coerce2 (#724): Does UEFN 43.12 refuse a local of type
# type{_(:int):int} used as a type{_(:int):void}, its result discarded (the
# Book's Void.versetest:91 names IntIdentity there, valid)? OpenVerse
# refuses it (a type error: no variance for values).
# OpenVerse refuses it: expected type{_(:int):void}, found type{_(:int):int}
IntIdentity(X:int):int = X
Run(F(:int):void):void = F(1)

Main():void =
    G:type{_(:int):int} = IntIdentity
    Run(G)
    Print("OVPROBE called")
