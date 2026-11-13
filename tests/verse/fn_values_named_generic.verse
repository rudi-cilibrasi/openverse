# Generic functions and methods with named parameters as values (#503): the
# expected function type determines their type arguments, named parameters'
# too, also an open type in generic code, with comparable bounds and tuple
# adapters; omitted defaults run in the function's scope.
Pick(X:t, ?Y:t = X where t:type):t = Y
Same(X:t, ?Y:t where t:subtype(comparable))<decides><computes>:t =
    X = Y
    X
Swap(P:tuple(a, b), ?Tag:string = "t" where a:type, b:type):tuple(b, a, string) = (P(1), P(0), Tag)
Apply(F:type{_(:t, ?Y:t):t}, X:t, Y:t where t:type):t = F(X, ?Y := Y)
ApplyOne(F:type{_(:t):t}, X:t where t:type):t = F(X)
Second(X:int, ?Y:int = 100):int = X + Y
pair(t:type) := class:
    First:t
    With(X:u, ?Other:t = First where u:type):tuple(u, t) = (X, Other)
Main():void =
    F:type{_(:int):int} = Pick
    G:type{_(:string, ?Y:string):string} = Pick
    Print("{F(3)} {G("a", ?Y := "b")}")
    Print("{Apply(Pick, 1, 2)} {ApplyOne(Pick, 4)} {Apply(Second, 1, 2)} {ApplyOne(Second, 1)}")
    S:type{_(:int, ?Y:int)<decides><computes>:int} = Same
    if (V := S[3, ?Y := 3]) then Print("same {V}")
    if (V := S[3, ?Y := 4]) then Print("bad") else Print("differs")
    W:type{_(:int, :string):tuple(string, int, string)} = Swap
    WT:type{_(:int, :string, ?Tag:string):tuple(string, int, string)} = Swap
    A := W(1, "a")
    B := WT(2, "b", ?Tag := "u")
    Print("{A(0)} {A(1)} {A(2)} {B(2)}")
    P := pair(int){First := 7}
    M:type{_(:string):tuple(string, int)} = P.With
    N:type{_(:logic, ?Other:int):tuple(logic, int)} = P.With
    R := M("x")
    Q := N(true, ?Other := 8)
    Print("{R(0)} {R(1)} {Q(1)}")
