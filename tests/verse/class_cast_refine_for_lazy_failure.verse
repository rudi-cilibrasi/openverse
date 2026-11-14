# Lazy producer clauses stay; rejected values roll back; body failure stops every producer.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Lazy(H:counter, N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("visit {N} {H.N}")
    N | Lazy[H, N - 1]
Fail(H:counter)<transacts><decides>:int =
    set H.N += 10
    Print("fail {H.N}")
    false?
    0
Use(P:pair(a, b), Q:pair(c, d), H:counter where a:type, b:type, c:type, d:type)<transacts><decides>:void =
    var Total:int = 0
    R := for (A := 1 | 2, (set Total += A; true?),
        V := if (D := dup[P]) then (D.C | D.C + 1) else 0,
        X := 1..2, L := Lazy[H, 1], (set Total += L; true?), L = 0,
        W := if (E := dup[Q]) then (E.C | E.C + 1) else 0):
        set Total += V + W
        Print("body {A} {V} {X} {L} {W} {Total} visits {H.N}")
        if (W = 5) then Fail[H] else Total
    Print("unreachable {R.Length}")
Main()<decides>:void =
    H := counter{}
    Use[dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"}, H]
