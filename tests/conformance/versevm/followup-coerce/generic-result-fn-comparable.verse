# followup-coerce (#724): generic-result-fn at t = comparable (the Book's
# ParametricFunctions.versetest:546: "Required so a function coercion isn't
# required"). OpenVerse's rule: an instance any or comparable needs no
# wrapper, admitted.
# OpenVerse (Lean and C agreeing) prints took
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
TakeComparable(X:comparable):void = Print("OVPROBE took")
Wrap(X:t, F(:t):void where t:type):(t->void) = F

Main():void =
    C:comparable = 1
    G := Wrap(C, TakeComparable)
    G(C)
