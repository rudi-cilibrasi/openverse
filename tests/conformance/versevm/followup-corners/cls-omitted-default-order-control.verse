# followup-corners (#724): Control for cls-omitted-default-order and struct-
# omitted-default-order: does UEFN admit a field default that constructs a
# class whose block prints (no order asked: every field is omitted)?
# OpenVerse (Lean and C agreeing): ran, default c | done 1 2.
# If Epic prints the same, the order probes ask only about order. If it
# refuses it, their refusal says nothing about order (OpenVerse would then
# refuse such a default too, if the reason is a rule of data members).
# Not yet compiled or run by UEFN.
marker := class:
    block:
        Print("OVPROBE default c")

holder := class:
    A:int = 1
    C:marker = marker{}
    B:int = 2

Main():void =
    H := holder{}
    Print("OVPROBE done {H.A} {H.B}")
