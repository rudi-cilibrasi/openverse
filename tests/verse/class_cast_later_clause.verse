# Casts as later clauses of an if's condition (#243, #351): a refining cast after a binding, an index, a
# comparison or an option's value, with and without an else; a cast through a view after a comparison; a
# plain cast there as it was
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (Y := 1, D := dup[P], D.C > Y) then X else P.B
G(P:pair(a, b), Ys:[]int where a:type, b:type):int =
    if (N := Ys[0], N > 0, D := dup[P]):
        D.C + N
    else:
        -1
H(P:pair(a, b), M:?int where a:type, b:type)<transacts>:void =
    if (V := M?, D := dup[P], D.C = V):
        Print("match {V}")
Plain(X:pair(int, int)):int =
    if (Y := 1, D := dup[X]) then D.C + Y else 0
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
one(u:type) := class(sink(u)):
    W:u
    Put<override>(X:u):int = 100
VW(S:sink(string), N:int):string =
    if (N > 0, O := one[S]) then "one {O.W}" else "not one"
Main()<transacts>:void =
    Print("{F(dup(int){A := 1, B := 2, C := 3}, 7)} {F(dup(int){A := 1, B := 2, C := 0}, 7)} {F(pair(int, string){A := 1, B := "x"}, 7)}")
    Print("{G(dup(int){A := 1, B := 2, C := 3}, array{5})} {G(dup(int){A := 1, B := 2, C := 3}, array{0})} {G(pair(int, int){A := 1, B := 2}, array{5})} {G(dup(int){A := 1, B := 2}, array{})}")
    H(dup(int){A := 1, B := 2, C := 4}, option{4})
    H(dup(int){A := 1, B := 2, C := 4}, option{5})
    H(dup(int){A := 1, B := 2, C := 4}, false)
    Print("{Plain(dup(int){A := 1, B := 1, C := 9})}")
    Print("{VW(one(string){W := "w"}, 1)} {VW(one(string){W := "w"}, 0)} {VW(both(int, string){V := 1}, 1)}")
