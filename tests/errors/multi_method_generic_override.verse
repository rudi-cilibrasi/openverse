# expect: 4:4: box.Both has several values, but a class that has it is generic (box) and it is overridden
box(t : type) := class:
    A : t
    Both()<transacts>:t = A | A
sbox(t : type) := class(box(t)):
    Both<override>()<transacts>:t = A
Main()<transacts>:void =
    X := box(int){A := 1}
    for (V := X.Both()):
        Print("{V}")
