# Interfaces and classes mixed (#283): an interface's method with several
# values and a default, overridden in a class, beside an unrelated class's
# family with an override of its own and a class whose method of the name
# is ordinary. A receiver typed as the interface, as a class below it or as
# a class of the other family dispatches in its own family.
shape := interface:
    Edge : int = 1
    Sides()<transacts>:int = Edge | Edge + 1
    Both()<transacts>:int = Sides() + Self.Sides() * 10
square := class(shape):
    Sides<override>()<transacts>:int = 4 | (super:)Sides()
circle := class(shape):
    Edge<override> : int = 100
base := class:
    Sides()<transacts>:int = 7
derived := class(base):
    Sides<override>()<transacts>:int = 8 | 9
plain := class:
    Sides()<transacts>:int = 0
# (a shape through a field)
frame := class:
    Inner : shape
    Sides()<transacts>:int = Inner.Sides() - 1 | -1
Main()<transacts>:void =
    Ss : []shape = array{square{}, circle{}}
    for (S : Ss, N := S.Sides()):
        Print("shape {N}")
    for (N := circle{}.Sides()):
        Print("circle {N}")
    for (N := square{}.Both()):
        Print("both {N}")
    B : base = derived{}
    for (N := B.Sides()):
        Print("base {N}")
    for (N := base{}.Sides()):
        Print("plain base {N}")
    Print("plain {plain{}.Sides()}")
    for (N := frame{Inner := circle{}}.Sides()):
        Print("frame {N}")
    if (N := frame{Inner := square{}}.Sides(), N > 0):
        Print("first {N}")
