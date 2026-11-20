# Book: Tests/Any.versetest:152;
# Tests/Bugs/SOL-3799-AddToMembersWhileIteratingOverThem.versetest:16 (2
# cases): a function named where a function type with an any result is
# expected, Succ (:int -> int) for G(:int):any (SOL-3799's case passes it
# through a generic Apply(F(:t):any, X:t)). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "expected type{_(:int):any},
# found type{_(:int):int}"
# If UEFN 43.12 admits it, it prints
#   succ of 0
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Succ(X:int):int =
    Print("OVPROBE succ of {X}")
    X + 1

Call(G(:int):any):any = G(0)

Main():void =
    Call(Succ)
