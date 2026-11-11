# A failed nested consumer stops the whole outer loop with its effects.
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
counter := class:
    var N:int = 0
Lazy(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("produce {N} {H.N}")
    N | Lazy[H,N-1]
Step(H:counter,V:int,L:int)<transacts><decides>:int =
    set H.N += V + L
    Print("step {V} {L} {H.N}")
    L > 0
    V + L
Run(P:pair(a,b),H:counter where a:type,b:type)<transacts><decides>:void =
    defer: Print("unexpected source cleanup")
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        defer: Print("unexpected body cleanup")
        for (L := Lazy[H,1]):
            Step[H,V,L]
    Print("unexpected suffix")
Main()<transacts><decides>:void = Run[dup(int){A:=1,B:=2},counter{}]
