# expect: 4:4: box.Vals has several values, but its class is generic: such 
box(t : type) := class:
    V : t
    Vals()<transacts>:t = V | V
Main()<transacts>:void =
    B := box(int){V := 1}
    for (X := B.Vals()):
        Print("{X}")
