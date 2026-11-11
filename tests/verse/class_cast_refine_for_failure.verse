pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Fail(H:counter)<transacts><decides>:int =
    set H.N += 10
    Print("fail {H.N}")
    false?
    0
Use(P:pair(a,b), H:counter where a:type,b:type)<transacts><decides>:void =
    var Total:int = 0
    R := for (A := 1 | 2, set Total += A,
        V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        set Total += V
        set H.N = Total
        Print("body {V} {Total}")
        if (V = 5) then Fail[H] else V
    Print("done {Total} {R.Length}")
Main()<transacts><decides>:void =
    H := counter{}
    Use[dup(int){A:=1,B:=2}, H]
