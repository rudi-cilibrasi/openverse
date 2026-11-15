Id(X:t where t:type):t = X
Dup(V:t where t:type):t = V | V
Keep(N:int,X:t where t:type):t =
    F:type{_(:t):t} = Id
    F(X) | F(X)
Keep(S:string,X:t where t:type):t =
    F:type{_(:t):t} = Id
    F(X) | F(X)
Main()<transacts>:void =
    var Count:int = 0
    for (P := 1..2, A := Dup(1) | Dup("x"), B := Keep(A,"ok"), C := Dup(2) | Dup("y"), D := Keep(C,B)):
        if (D = "ok"): set Count += 1
    Print("count {Count}")
    if (A := Dup(1) | Dup("x"), B := Keep(A,"ok"), B = "ok"): Print("first {B}")
    O := option{A := Dup(1) | Dup("x"); B := Keep(A,"ok"); B = "ok"; B}
    if (B := O?): Print("option {B}")
