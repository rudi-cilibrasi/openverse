# GetSecondsSinceEpoch (#724; the Book's Runtime API reference,
# /Verse.org/Verse; UEFN 43.12 admits and runs it,
# followup-refused/get-seconds-since-epoch). openverse is deterministic
# (LANGUAGE.md, "Random numbers, the clock and the player map"): its clock
# is frozen at 2026-11-20T00:00:00Z, also across a Sleep; two calls agree,
# as the Book's tests ask (GetSecondsSinceEpoch.versetest:6), and the value
# is after the day the test was written (:12).
Stamp()<reads>:float = GetSecondsSinceEpoch()
Main()<suspends>:void =
    A := GetSecondsSinceEpoch()
    B := GetSecondsSinceEpoch()
    if (A = B, A > 1716411409.0) then Print("clock {A}")
    Sleep(2.0)
    if (Stamp() = A) then Print("frozen")
