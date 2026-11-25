# followup-corners (#724): cls-omitted-default-order with holder a struct:
# where does a struct's omitted default run among the values an archetype
# gives out of declaration order?
# OpenVerse (Lean and C agreeing): ran, value b | default c | value a | done
# 10 20 (as a class's).
# If Epic prints the same, OpenVerse agrees. Another order (value b | value
# a | default c, or default c first) would be a struct's rule, perhaps not a
# class's: OpenVerse would take it. If Epic refuses it, see struct-omitted-
# default-order-control (a struct may not hold or construct such a class).
# Not yet compiled or run by UEFN.
Note(S:string, V:int):int =
    Print("OVPROBE value {S}")
    V

marker := class:
    block:
        Print("OVPROBE default c")

holder := struct:
    A:int = 1
    C:marker = marker{}
    B:int = 2

Main():void =
    H := holder{B := Note("b", 20), A := Note("a", 10)}
    Print("OVPROBE done {H.A} {H.B}")
