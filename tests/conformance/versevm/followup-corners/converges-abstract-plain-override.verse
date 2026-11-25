# followup-corners (#724): The same overridden by a method with no effect
# specifier.
# OpenVerse (Lean and C agreeing): refused, the same message as converges-
# abstract-computes-override.
# If Epic refuses it, OpenVerse agrees on the verdict; which error (3565 at
# the declaration, or an effect mismatch at the override) says whether a
# bodyless <converges> method is admitted at all. If it admits it and prints
# sides 4, OpenVerse would admit it.
# Not yet compiled or run by UEFN.
shape := class<abstract>:
    Sides()<converges>:int

square := class(shape):
    Sides<override>():int = 4

Main():void =
    S:shape = square{}
    Print("OVPROBE sides {S.Sides()}")
