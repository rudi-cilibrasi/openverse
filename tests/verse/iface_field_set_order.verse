# from the review of #57 (p1): interface field sets at different positions
counted := interface:
    var Count:int = 0
named := interface:
    Name:string = "?"
a := class(counted, named):
    Extra:int = 1
b := class(named, counted):
    Other:int = 2
abs := class<abstract>(named):
    Q:int = 0
c := class(abs, counted):
    W:int = 3
d := class(c):
    V:int = 4
e := class(named):
    P:int = 5
f := class(e, counted):
    R:int = 6
Obj(C:counted, S:string)<transacts>:counted =
    Print("obj {S}")
    C
Val(N:int, S:string)<transacts>:int =
    Print("val {S}")
    N
Main():void =
    Cs:[]counted = array{a{}, b{}, c{}, d{}, f{}}
    for (I := 0..4):
        if (set Cs[Val(I, "i")].Count = Val(10, "r")) {}
    for (C : Cs) { Print("{C.Count}") }
    for (C : Cs):
        set C.Count += Val(1, "p")
        set C.Count -= 3
        set C.Count *= 2
    for (C : Cs) { Print("{C.Count}") }
    for (C : Cs):
        if (set C.Count = 5, false?) {}
        if (set C.Count += 100, Val(0, "f") > 1) {}
    for (C : Cs) { Print("{C.Count}") }
    if (X := set Cs[0].Count = 77) then Print("{X} {Cs[0].Count or -1}")
