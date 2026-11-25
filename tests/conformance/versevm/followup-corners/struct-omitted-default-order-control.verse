# followup-corners (#724): Control for struct-omitted-default-order: does
# UEFN admit a struct with a field of a class type whose default constructs
# a class whose block prints (every field omitted)?
# OpenVerse (Lean and C agreeing): ran, default c | done 1 2.
# If Epic prints the same, struct-omitted-default-order asks only about
# order. If it refuses it, that probe's refusal says nothing about order.
# Not yet compiled or run by UEFN.
marker := class:
    block:
        Print("OVPROBE default c")

holder := struct:
    A:int = 1
    C:marker = marker{}
    B:int = 2

Main():void =
    H := holder{}
    Print("OVPROBE done {H.A} {H.B}")
