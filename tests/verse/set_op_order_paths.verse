# set P op= e and V := e; set P = P + V agree, also when e changes the option, map or array (#58
# review): e runs first, then P's old value is read from what e left (the Book of Verse's tests,
# ArrayAppend.versetest 140 and 183)
sub := struct:
    F:int = 0
    G:int = 0
hold := class:
    var O:?int = false
    var M:[int]int = map{}
    var A:[]int = array{1, 2}
    var Sub:sub = sub{}
FillO(H:hold)<transacts>:int =
    set H.O = option{10}
    1
EmptyO(H:hold)<transacts>:int =
    set H.O = false
    1
ClearM(H:hold)<transacts>:int =
    set H.M = map{}
    1
FillM(H:hold)<transacts>:int =
    set H.M = map{5 => 50}
    1
GrowA(H:hold)<transacts>:int =
    set H.A = array{1, 2, 3, 4, 5, 6}
    1
ShrinkA(H:hold)<transacts>:int =
    set H.A = array{}
    1
NewSub(H:hold)<transacts>:int =
    set H.Sub = sub{F := 100, G := 200}
    1
Show(T:string, H:hold, Ok:logic):void =
    Print("{T} {if (Ok?) then "ok" else "fail"} {H.O? or -1} {H.M[5] or -1} {H.A.Length} {H.A[4] or -1} {H.Sub.F} {H.Sub.G}")
Main():void =
    for (D := 0..1):
        H := hold{}
        Ok1 := logic{if (D = 0) then (set H.O? += FillO(H)) else (V := FillO(H); set H.O? = H.O? + V)}
        Show("fillO{D}", H, Ok1)
        H2 := hold{O := option{3}}
        Ok2 := logic{if (D = 0) then (set H2.O? += EmptyO(H2)) else (V := EmptyO(H2); set H2.O? = H2.O? + V)}
        Show("emptyO{D}", H2, Ok2)
        H3 := hold{M := map{5 => 7}}
        Ok3 := logic{if (D = 0) then (set H3.M[5] += ClearM(H3)) else (V := ClearM(H3); set H3.M[5] = H3.M[5] + V)}
        Show("clearM{D}", H3, Ok3)
        H4 := hold{}
        Ok4 := logic{if (D = 0) then (set H4.M[5] += FillM(H4)) else (V := FillM(H4); set H4.M[5] = H4.M[5] + V)}
        Show("fillM{D}", H4, Ok4)
        H5 := hold{}
        Ok5 := logic{if (D = 0) then (set H5.A[4] += GrowA(H5)) else (V := GrowA(H5); set H5.A[4] = H5.A[4] + V)}
        Show("growA{D}", H5, Ok5)
        H6 := hold{}
        Ok6 := logic{if (D = 0) then (set H6.A[1] += ShrinkA(H6)) else (V := ShrinkA(H6); set H6.A[1] = H6.A[1] + V)}
        Show("shrinkA{D}", H6, Ok6)
        H7 := hold{Sub := sub{F := 1, G := 2}}
        if (D = 0) then (set H7.Sub.F += NewSub(H7)) else (V := NewSub(H7); set H7.Sub.F = H7.Sub.F + V)
        Show("newSub{D}", H7, true)
