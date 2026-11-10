# expect: 6:4: k.M has several values, but an interface that has it is generic (i) and it is overridden
i(t : type) := interface:
    M()<transacts>:t
k(t : type) := class(i(t)):
    X : t
    M<override>()<transacts>:t = X | X
Main()<transacts>:void =
    for (V := k(int){X := 1}.M()):
        Print("{V}")
