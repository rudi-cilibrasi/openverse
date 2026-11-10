# expect: 4:4: box.Both has several values, but ibox overrides it and gives box, which is generic, type arguments other than its own type parameters
box(t : type) := class:
    A : t
    Both()<transacts>:t = A | A
ibox := class(box(int)):
    Both<override>()<transacts>:int = A + 100
Main()<transacts>:void =
    for (V := ibox{A := 1}.Both()):
        Print("{V}")
