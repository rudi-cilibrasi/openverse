pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
counter := class:
    var N:int = 0
Operand(H:counter,N:int)<transacts>:int =
    set H.N += 1
    Print("operand {N} {H.N}")
    N
Run(P:pair(a,b),Q:pair(c,d),H:counter,Stop:int where a:type,b:type,c:type,d:type)<suspends>:int =
    Sleep(0.0)
    var Total:int = 0
    defer: Print("source {Total} {H.N}")
    R := for (A := 1 | 2, set Total += A,
        V := if (D := dup[P]) then (D.C | D.C + 1) else 0,
        set Total += V,
        W := if (E := dup[Q]) then (E.C | E.C + 1) else 0):
        defer:
            set Total += 100
            Print("body cleanup {Total}")
        set Total += W
        Print("body {A} {V} {W} {Total}")
        if (V + W = Stop):
            return Operand(H, Total)
        V + W
    Print("done {Total} {R.Length}")
    -1
Typed(P:pair(a,b) where a:type,b:type)<suspends>:b =
    Sleep(0.0)
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        if (E := dup[P]):
            return E.A
    P.B
Nested(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    Sleep(0.0)
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        for (W := if (E := dup[Q]) then (E.C | E.C + 1) else 0):
            Print("nested {V} {W}")
            if (W = 5):
                return V + W
    -1
Void(P:pair(a,b) where a:type,b:type)<suspends>:void =
    Sleep(0.0)
    defer: Print("void source")
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        defer: Print("void body")
        Print("void {V}")
        return
    Print("void unexpected")
FilterBreak()<suspends>:int =
    Sleep(0.0)
    var N:int = 0
    loop:
        defer: Print("loop cleanup {N}")
        R := for (A := 1 | 2, if (A = 2) then break else Print("filter {A}")):
            set N += A
            if (false?):
                return -9
            A
        Print("unexpected after for")
    N
Main()<suspends>:void =
    P := dup(int){A:=1,B:=2}
    Q := dup(string){A:="a",B:="b"}
    H := counter{}
    Print("returned {Run(P,Q,H,9)}")
    Print("typed {Typed(P)}")
    Print("typed {Typed(pair(int,string){A:=1,B:="s"})}")
    Print("nested result {Nested(P,Q)}")
    Void(P)
    Print("break result {FilterBreak()}")
