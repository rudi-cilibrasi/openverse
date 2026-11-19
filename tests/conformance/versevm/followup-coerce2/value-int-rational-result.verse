# followup-coerce2 (#724): Does UEFN 43.12 admit or refuse a local of type
# type{_(:int):int} used as a type{_(:int):rational}? OpenVerse refuses it
# (a type error: no variance for values).
# OpenVerse refuses it: expected type{_(:int):rational}, found
# type{_(:int):int}
Twice(X:int):int = 2 * X
Run(F(:int):rational):int = Floor(F(3))

Main():void =
    G:type{_(:int):int} = Twice
    Print("OVPROBE value {Run(G)}")
