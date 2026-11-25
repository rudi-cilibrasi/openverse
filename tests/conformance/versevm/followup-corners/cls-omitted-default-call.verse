# followup-corners (#724): The question as first written: the omitted
# field's default calls a printing function, C:int = Note("c", 3), Note
# <transacts>. Expected: refused by Epic (3582, as followup-3582/div-field-
# default-call).
# OpenVerse (Lean and C agreeing): refused, the default of field 'C' of
# holder calls Note, which might not complete (3582).
# If Epic refuses it (3582), OpenVerse agrees. If it admits it, a
# <transacts> function may be called in a field default, and it prints the
# order itself: OpenVerse (--extended-defaults) prints value b | value c |
# value a | done 10 20 3.
# Not yet compiled or run by UEFN.
Note(S:string, V:int)<transacts>:int =
    Print("OVPROBE value {S}")
    V

holder := class:
    A:int = 1
    C:int = Note("c", 3)
    B:int = 2

Main():void =
    H := holder{B := Note("b", 20), A := Note("a", 10)}
    Print("OVPROBE done {H.A} {H.B} {H.C}")
