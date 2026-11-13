# function values and effects (#210): a function with fewer effects is a
# value of a type with more, also between variables; literals join their
# elements' types whatever their order; a var holding a function is rolled
# back with a failure context; a field named like a function in one class
# leaves it a value elsewhere
Pure(X:int)<computes>:int = X
Plain(X:int):int = X + 1
Rd(X:int)<reads>:int = X + 2
D(X:int)<decides>:int =
    X > 0
    X * 10
Use(F:int->int):int = F(1)
UseD(F:type{_(:int)<decides>:int}):int = if (Y := F[1]) then Y else -1
a := class:
    (a:)Double:int = 7
b := class:
    Get():int->int = Double
Double(X:int):int = 2 * X
Main():void =
    P:type{_(:int)<computes>:int} = Pure
    R:type{_(:int)<reads>:int} = P
    Q:int->int = R
    Print("{Use(P)} {Use(R)} {Use(Q)} {UseD(Q)} {UseD(D)}")
    Xs := array{Plain, Pure}
    Ys := array{Pure, Plain}
    Zs := array{Rd, D}
    M := map{1 => Pure, 2 => Plain}
    Print("{Xs.Length} {Ys.Length} {Zs.Length}")
    for (F : Ys) { Print("{F(5)}") }
    for (F : Zs, Y := F[5]) { Print("{Y}") }
    if (F := M[2]) then Print("{F(5)}")
    var V:int->int = Plain
    if (set V = Double, D[-1]) then Print("set") else Print("rolled back")
    Print("{V(5)}")
    Print("{b{}.Get()(5)} {a{}.Double}")
