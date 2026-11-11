box(t:type) := struct { E:[]t = Concatenate(); B:int }
meter := class:
    var N:int = 0
Nat(H:meter, N:int)<transacts><decides>:int =
    N <= 3
    set H.N += 1
    Print("visit {N}")
    N | Nat[H,N+1]
Search(Unused:t, H:meter where t:type)<transacts>:int =
    if (I := Nat[H,0], B:box(t) = box{B := 1 | 2}, I + B.B >= 3) then I + B.B + B.E.Length else -1
Main():void =
    H := meter{}
    Print("string {Search("s", H)}")
    Print("int {Search(1, H)}")
    Print("visits {H.N}")
