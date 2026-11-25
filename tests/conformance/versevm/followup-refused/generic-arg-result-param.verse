# Book: Tests/ParametricFunctions.versetest:192 (1 case): a generic function
# passed to a generic Apply whose second type parameter, u, only the
# argument's result gives (Apply(Identity, 1) with one type parameter is
# admitted, followup-coerce/generic-arg-generic). The Book's tests expect it
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "cannot infer type parameter
# u of Apply from the arguments of this call"
# If UEFN 43.12 admits it, it prints
#   value 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Identity(X:t where t:type):t = X

Apply(F(:t):u, X:t where t:type, u:type):u = F(X)

Main():void =
    Print("OVPROBE value {Apply(Identity, 1)}")
