# followup-corners (#724): A method without a body declared <converges> in
# an <abstract> class, overridden by a <computes> method with a body. (Epic:
# 3565, "The 'converges' effect is only allowed on native functions",
# followup-3582/div-const-converges, a function with a body.)
# OpenVerse (Lean and C agreeing): refused, shape.Sides is <converges>, so
# Sides cannot override it with a body: only a native function or a method
# without a body may be <converges> (3565), and an override has no effect
# the method it overrides lacks.
# If Epic refuses it, at the declaration (3565) or at the override,
# OpenVerse agrees on the verdict. If it admits it and prints sides 4, a
# <computes> body may override a <converges> declaration: OpenVerse would
# admit it.
# Not yet compiled or run by UEFN.
shape := class<abstract>:
    Sides()<converges>:int

square := class(shape):
    Sides<override>()<computes>:int = 4

Main():void =
    S:shape = square{}
    Print("OVPROBE sides {S.Sides()}")
