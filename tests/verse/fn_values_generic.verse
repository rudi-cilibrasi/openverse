# function values in generic code (#210): a generic function over a function
# type, called with functions that fix its type arguments (under the
# refinement, #142); a function passed where a <decides> one is expected; a
# function-typed field of a generic class
Double(X:int):int = 2 * X
Show(X:int):string = "<{X}>"
Echo(S:string):string = S + S
Half(X:int)<decides>:int =
    X > 2
    X - 2
Map(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }
Filter(Xs:[]int, F:type{_(:int)<decides>:int}):[]int = for (X : Xs, Y := F[X]) { Y }
box(t:type) := class:
    V:t
    F:type{_(:t):t}
    Go():t = F(V)
Neg(X:int):int = -X
Main():void =
    for (S : Map(array{1, 2, 3}, Show)) { Print(S) }
    Ys := Map(array{1, 2}, Double)
    for (Y : Ys) { Print("{Y}") }
    Zs := Filter(array{1, 2, 3, 4}, Half)
    Print("{Zs.Length}")
    Ws := Filter(array{1, 2}, Double)
    Print("{Ws.Length}")
    B := box(int){V := 4, F := Neg}
    S := box(string){V := "s", F := Echo}
    Print("{B.Go()} {S.Go()}")
    if (Half[2]) then Print("half") else Print("small")
