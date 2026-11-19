# followup-coerce2 (#724): Does UEFN 43.12 admit a function of a rational
# named where a type{_(:int):int} is expected (a parameter int to rational,
# by a name)? OpenVerse admits it (#214).
# OpenVerse (Lean and C agreeing) prints value 3
Half(X:rational):int = Floor(X)
Run(F(:int):int):int = F(3)

Main():void =
    Print("OVPROBE value {Run(Half)}")
