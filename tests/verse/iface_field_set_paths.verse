# from the review of #57 (p2): interface field sets at different positions
sub := struct<computes>:
    F:int = 0
    G:int = 0
named := interface:
    Name:string = "?"
holds := interface:
    var Arr:[]int = array{0, 0}
    var Sub:sub = sub{}
    var M:[int]int = map{}
    var O:?int = false
a := class(holds, named):
    Extra:int = 1
b := class(named, holds):
    Other:int = 2
abs := class<abstract>(named):
    Q:int = 0
c := class(abs, holds):
    W:int = 3
d := class(c):
    V:int = 4
Val(N:int, S:string)<transacts>:int =
    Print("val {S}")
    N
Show(H:holds):void =
    Print("{H.Arr[0] or -1} {H.Arr[1] or -1} {H.Sub.F} {H.Sub.G} {H.M[1] or -1} {H.O? or -1}")
Main():void =
    Hs:[]holds = array{a{}, b{}, c{}, d{}}
    for (H : Hs):
        if (set H.Arr[Val(1, "i")] = Val(7, "r")) {}
        set H.Sub.G = 8
        set H.Sub.F += 2
        if (set H.M[1] = 9) {}
        set H.O = option{4}
        if (set H.O? += 1) {}
        if (set H.Arr[5] = 1) {}
        if (set H.Arr[0] = 3, false?) {}
        if (set H.Sub.F = 50, false?) {}
        Show(H)
