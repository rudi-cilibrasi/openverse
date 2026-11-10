# A generic class's method with several values and named parameters (#283): its type arguments inferred from the receiver, a default reading a field
box(t : type) := class:
    A : t
    B : t
    Pick(?W : t = A)<transacts>:t = W | B
Main()<transacts>:void =
    X := box(int){A := 1, B := 2}
    for (V := X.Pick()):
        Print("1 {V}")
    for (V := X.Pick(?W := 5)):
        Print("2 {V}")
