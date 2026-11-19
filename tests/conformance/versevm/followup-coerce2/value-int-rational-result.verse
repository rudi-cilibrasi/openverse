# followup-coerce2 (#724): Does UEFN 43.12 admit or refuse a local of type
# type{_(:int):int} used as a type{_(:int):rational}? OpenVerse refused it
# as a type error (no variance for values) until Epic answered, and now
# cites 3502.
# OpenVerse refuses it: 3502 rule: using a value of type type{_(:int):int}
# as a value of type type{_(:int):rational}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L11 "Using a value of type int->int as a value of type
# int->rational is not yet implemented."
Twice(X:int):int = 2 * X
Run(F(:int):rational):int = Floor(F(3))

Main():void =
    G:type{_(:int):int} = Twice
    Print("OVPROBE value {Run(G)}")
