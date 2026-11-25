# followup-corners (#724): An archetype gives B then A, holder{B :=
# Note("b", 20), A := Note("a", 10)}, and omits C, declared between A and B,
# whose default constructs a class whose block prints: where does the
# omitted default run among the given values? (Epic ran the given values in
# the order written, differential/cls-construction-order; a default that
# calls a function is refused, 3582, so the default is an archetype.)
# OpenVerse (Lean and C agreeing): ran, value b | default c | value a | done
# 10 20 (the given values, in the order written, take the places the given
# fields have in declaration order; an omitted default runs at its own
# place).
# If Epic prints the same, OpenVerse agrees. value b | value a | default c:
# omitted defaults run after every given value; default c | value b | value
# a: before them; OpenVerse would take either order. If Epic refuses it and
# the control too, a field default cannot construct a class whose block
# prints and the question needs another observable.
# Not yet compiled or run by UEFN.
Note(S:string, V:int):int =
    Print("OVPROBE value {S}")
    V

marker := class:
    block:
        Print("OVPROBE default c")

holder := class:
    A:int = 1
    C:marker = marker{}
    B:int = 2

Main():void =
    H := holder{B := Note("b", 20), A := Note("a", 10)}
    Print("OVPROBE done {H.A} {H.B}")
