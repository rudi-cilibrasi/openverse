# expect: 3:0: Twice has several values, is generic and writes a type that mentions its type parameters in its body
# (#235) a type written in its body would name its type parameter where its body is inlined
Twice(X:t where t:type):t =
    Y:t = X
    Y | X
Main():void =
    for (Z := Twice(1)) { Print("{Z}") }
