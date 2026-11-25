# followup-corners (#724): Control for the two converges-abstract probes:
# the same classes with <computes> for <converges>, overridden by a
# <computes> method.
# OpenVerse (Lean and C agreeing): ran, sides 4.
# If Epic prints sides 4, a refusal of the other two is about <converges>.
# If it refuses this, their refusals say nothing about <converges>.
# Not yet compiled or run by UEFN.
shape := class<abstract>:
    Sides()<computes>:int

square := class(shape):
    Sides<override>()<computes>:int = 4

Main():void =
    S:shape = square{}
    Print("OVPROBE sides {S.Sides()}")
