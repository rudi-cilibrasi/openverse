# followup-coerce2 (#724): Does UEFN 43.12 refuse a local of type
# type{_(:int):int} used as a type{_(:int):void}, its result discarded (the
# Book's Void.versetest:91 names IntIdentity there, valid)? OpenVerse
# refused it as a type error (no variance for values) until Epic answered,
# and now cites 3502.
# OpenVerse refuses it: 3502 rule: using a value of type type{_(:int):int}
# as a value of type type{_(:int):void}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L11 "Using a value of type int->int as a value of type
# int->void is not yet implemented."
IntIdentity(X:int):int = X
Run(F(:int):void):void = F(1)

Main():void =
    G:type{_(:int):int} = IntIdentity
    Run(G)
    Print("OVPROBE called")
