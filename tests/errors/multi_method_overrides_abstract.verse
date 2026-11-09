# expect: 7:0: c must implement M (declared abstract in a)
# (an abstract one implemented)
a := class<abstract>:
    M()<transacts>:int
b := class(a):
    M<override>()<transacts>:int = 1 | 2
c := class(a):
    X : int = 0
Main()<transacts>:void =
    O : a = c{}
    for (V := O.M()):
        Print("{V}")
    Print("done")
