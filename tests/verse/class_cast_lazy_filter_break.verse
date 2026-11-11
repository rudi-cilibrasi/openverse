# Cast exits must set the caller's source-break target after copy-outs.
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
counter := class:
    var N:int = 0
Trace(H:counter,N:int)<transacts>:int =
    set H.N += 1
    Print("produce {N} {H.N}")
    N
Lazy(H:counter,N:int)<transacts><decides>:int =
    N >= 0
    V := Trace(H,N)
    V | Lazy[H,N-1]
Run(P:pair(a,b),H:counter where a:type,b:type)<transacts>:int =
    var Total:int = 0
    loop:
        defer: Print("cast loop {Total}")
        for (A := Lazy[H,2], if (D := dup[P]):
            set Total += D.C
            if (A = 1) then break else Print("cast keep {A}")
        else:
            Print("cast miss {A}")):
            set Total += A
            Print("cast body {Total}")
        Print("cast completed")
        break
    Total
Fails(P:pair(a,b),H:counter where a:type,b:type)<transacts><decides>:int =
    loop:
        for (A := Lazy[H,2], if (A = -1) then break else Print("guard {A}"),
            V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            if (V = 99):
                return V
            Print("failed body {A} {V}")
            false?
            V
        Print("unexpected failed suffix")
        break
    -1
Main()<transacts>:void =
    H := counter{}
    P := dup(int){A:=1,B:=2}
    Print("cast result {Run(P,H)}")
    Print("miss result {Run(pair(int,string){A:=1,B:="s"},H)}")
    if (R := Fails[P,H]) then Print("unexpected success {R}") else Print("caught {H.N}")
