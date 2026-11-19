# followup-coerce (#724): Does UEFN 43.12 admit Identity passed directly to
# a generic function whose parameter's function type has its type parameter,
# the function first (the Book's ParametricFunctions.versetest:192, valid on
# both VMs; Plus(One, ...) is refused, generic-higher-order)? OpenVerse
# admits it: Identity has no type parameter inside a function type of its
# own.
# OpenVerse (Lean and C agreeing) prints value 1
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
Identity(X:t where t:type):t = X
Apply(F(:t):t, X:t where t:type):t = F(X)

Main():void =
    Print("OVPROBE value {Apply(Identity, 1)}")
