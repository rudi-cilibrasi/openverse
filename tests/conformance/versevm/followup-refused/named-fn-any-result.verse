# Book: Tests/Any.versetest:152;
# Tests/Bugs/SOL-3799-AddToMembersWhileIteratingOverThem.versetest:16 (2
# cases): a function named where a function type with an any result is
# expected, Succ (:int -> int) for G(:int):any (SOL-3799's case passes it
# through a generic Apply(F(:t):any, X:t)). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "expected type{_(:int):any},
# found type{_(:int):int}"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   succ of 0
# OpenVerse now prints it too (#724, Lean and C): a function named where a
# function type with an any result is expected is converted, as at a void
# result (tests/verse/fn_named_any_result); a function value that is not named
# is still refused, as Epic refuses it (3502).
Succ(X:int):int =
    Print("OVPROBE succ of {X}")
    X + 1

Call(G(:int):any):any = G(0)

Main():void =
    Call(Succ)
