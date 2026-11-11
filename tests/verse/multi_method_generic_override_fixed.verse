# A fixed class override keeps the declaring family's result type.
box(t : type) := class:
    A : t
    Both()<transacts>:t = A | A
ibox := class(box(int)):
    Both<override>()<transacts>:int = A + 100
Main()<transacts>:void =
    for (V := ibox{A := 1}.Both()):
        Print("{V}")
