# expect: 4:4: box.Vals has several values, but a class that has it is generic
box(t : type) := class:
    V : t
    Vals()<transacts>:t = V | V
Main()<transacts>:void =
    B := box(int){V := 1}
    for (X := B.Vals()):
        Print("{X}")
