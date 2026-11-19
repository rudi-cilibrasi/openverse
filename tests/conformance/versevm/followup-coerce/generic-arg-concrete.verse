# followup-coerce (#724): Does UEFN 43.12 admit a generic function
# (Identity) passed directly as the argument of a function whose parameter
# is of a function type without type parameters (the Book's
# ParametricFunctions.versetest:182, valid on both VMs)? OpenVerse admits
# it.
# OpenVerse (Lean and C agreeing) prints value 1
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
Identity(X:t where t:type):t = X
ApplyInt(F(:int):int, X:int):int = F(X)

Main():void =
    Print("OVPROBE value {ApplyInt(Identity, 1)}")
