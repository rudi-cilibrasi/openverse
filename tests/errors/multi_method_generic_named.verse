# expect: 5:4: box.Pick has several values and named parameters, and is a method of a generic class
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
