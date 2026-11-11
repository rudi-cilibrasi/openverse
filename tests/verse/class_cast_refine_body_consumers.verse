# Prepared consumers and body cleanup remain inside the selected cast path.
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
Even(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("even {N} {H.N}")
    N | Odd[H,N-1]
Odd(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("odd {N} {H.N}")
    N | Even[H,N-1]
Run(P:pair(a,b),Q:pair(c,d),H:counter where a:type,b:type,c:type,d:type)<transacts>:int =
    var Total:int = 0
    R := for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0,
        W := if (E := dup[Q]) then (E.C | E.C + 1) else 0):
        defer:
            set Total += 100
            Print("body cleanup {Total}")
        A := for (L := Lazy[H,1], L >= 0):
            set Total += V + W + L
            Print("all {V} {W} {L} {Total}")
            L
        if (S := Even[H,2], set Total += S, Print("try {S}"), S < 1):
            Print("first {S} {Total}")
        else:
            Print("none")
        if (S := Even[H,1], set Total += S, Print("reject {S}"), S < 0):
            Print("unexpected rejected success")
        else:
            Print("rejected {Total} {H.N}")
        A.Length
    Print("state {Total} {H.N} {R.Length}")
    Total
Handled(P:pair(a,b),H:counter where a:type,b:type)<transacts>:int =
    var Total:int = 0
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        set Total += V
        O := option{
            for (L := Lazy[H,1]):
                Print("lost {L}")
                false?
                L
        }
        if (O?) then Print("unexpected") else Print("caught {V} {Total} {H.N}")
    Total
ReturnWithCleanup(P:pair(a,b),H:counter where a:type,b:type)<transacts>:int =
    var Total:int = 0
    defer: Print("return source {Total} {H.N}")
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        defer:
            set Total += 100
            Print("return cleanup {Total}")
        for (L := Lazy[H,1]):
            set Total += V + L
            Print("return body {V} {L} {Total}")
            if (L = 0):
                return Total
    -1
Main()<transacts>:void =
    P := dup(int){A:=1,B:=2}
    Q := dup(string){A:="a",B:="b"}
    H := counter{}
    Print("result {Run(P,Q,H)}")
    Print("handled {Handled(P,H)}")
    Print("miss {Handled(pair(int,string){A:=1,B:="s"},H)}")
    Print("returned {ReturnWithCleanup(P,H)}")
