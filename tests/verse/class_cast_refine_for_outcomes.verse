# Independent casts, enclosing transactions, nested loops and recursive calls.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Recur(H:counter, N:int)<transacts><decides>:int =
    set H.N += 1
    Print("recur {N} {H.N}")
    if (N > 0) then Recur[H, N - 1] else 7
Collect(P:pair(a,b), Q:pair(c,d), H:counter where a:type,b:type,c:type,d:type)<transacts><decides>:[]int =
    var Total:int = 0
    for (A := 1 | 2, set Total += A,
        V := if (D := dup[P]) then (D.C | D.C + 1) else 0,
        V > 0, set Total += V,
        W := if (E := dup[Q]) then (E.C | E.C + 1) else 0):
        set Total += W
        Print("body {A} {V} {W} {Total}")
        if (option{Print("lost"); false?}?) then Print("bad") else Print("kept")
        Z := for (B := 1 | 2, B > 1):
            Recur[H, B - 1]
        V + W + Z.Length
Main()<suspends>:void =
    P := dup(int){A:=1,B:=2}
    Q := dup(string){A:="a",B:="b"}
    H := counter{}
    if (Values := Collect[P, Q, H]):
        Print("done {Values.Length} {H.N}")
    else:
        Print("unexpected")
    if (Values := Collect[pair(int,string){A:=1,B:="s"}, Q, H]):
        Print("empty {Values.Length} {H.N}")
    else:
        Print("unexpected")
