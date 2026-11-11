# Returns and failures must cross lazy loops before leaving their source loop.
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
    Print("lazy {N} {H.N}")
    N | Lazy[H,N-1]
Single(P:pair(a,b),H:counter where a:type,b:type)<transacts>:int =
    var Total:int = 0
    defer: Print("single source {Total}")
    loop:
        defer: Print("single loop {Total}")
        for (L := Lazy[H,2], V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            defer: Print("single body {Total}")
            set Total += L + V
            return Total
        Print("unexpected single suffix")
        break
    -1
Double(P:pair(a,b),H:counter where a:type,b:type)<transacts>:int =
    var Total:int = 0
    defer: Print("double source {Total}")
    loop:
        defer: Print("double loop {Total}")
        for (L := Lazy[H,2], K := Lazy[H,2],
            V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            defer: Print("double body {Total}")
            set Total += L + K + V
            return Total
        Print("unexpected double suffix")
        break
    -1
Fails(P:pair(a,b),H:counter where a:type,b:type)<transacts><decides>:int =
    loop:
        for (L := Lazy[H,2], V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            if (V = 999):
                return V
            Print("failed body {L} {V}")
            false?
            V
        Print("unexpected failure suffix")
        break
    -1
Main()<transacts>:void =
    P := dup(int){A:=1,B:=2}
    H := counter{}
    Print("single result {Single(P,H)}")
    Print("double result {Double(P,H)}")
    if (R := Fails[P,H]) then Print("unexpected success {R}") else Print("caught {H.N}")
