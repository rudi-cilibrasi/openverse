# Generic functions with several values and named parameters (#283): a type argument that only an
# omitted default determines, as at a call (#392's review), also through an option, an overload, and a
# later default using an earlier one's type
F(X:int, ?Y:t = X where t:type)<transacts>:int = X | X + 1
G(X:int, ?Y:?t = option{X} where t:type)<transacts>:int = X | X * 10
H(X:string, ?Y:t = X where t:type)<transacts>:t = Y | Y
H(X:int, ?Y:int = 7)<transacts>:int = X | Y
K(X:int, ?Y:t = X, ?Zs:[]t = array{Y, Y} where t:type)<transacts>:t = Y | (if (Z := Zs[1]) then Z else Y)
Main()<transacts>:void =
    for (V := F(1)) { Print("a {V}") }
    for (V := G(2)) { Print("b {V}") }
    for (V := H("s")) { Print("c {V}") }
    for (V := H(3)) { Print("d {V}") }
    for (V := K(4)) { Print("e {V}") }
    for (V := K(4, ?Y := "y")) { Print("f {V}") }
