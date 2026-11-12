# A break in clauses that run as a function of their own (#283): after a
# composed choice another one follows (#335's continuation), or an
# effectful recursive generator is taken lazily (#246). The function gives
# the break back, with the vars it set, and the caller breaks.
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int = 4 }
cell := class { var N:int = 0 }
Two(N:int):int = N | N + 1
Early(N:int):int =
    if (N < 0): return 0
    N | N + 1
Upto(H:cell, A:int, B:int)<transacts><decides>:int =
    A <= B
    set H.N += 1
    Print("visit {A} {H.N}")
    A | Upto[H, A + 1, B]
# composed choices, a break or a return after them
Composed(Mode:int)<transacts>:int =
    var V:int = 0
    defer: Print("function cleanup V={V}")
    loop:
        defer: Print("loop cleanup V={V}")
        if (A := (Two(0) | Two(2)), set V += 1, B := (Two(0) | Two(2)), set V += 10,
            if (A + B = Mode) then break else 0, A + B = 5, Print("ab {A} {B}"), return 100 + V):
            Print("not reached")
        Print("no success")
        break
    V
# exclusive choices, then the lazy generator with effects
Exclusive(H:cell)<transacts>:int =
    var V:int = 0
    loop:
        defer: Print("loop cleanup V={V} H={H.N}")
        if (A := Early(1), B := Early(A), set V += A * 10 + B, X := Upto[H, B, 9], X > 3, break):
            Print("not reached")
    V
# a refining choice, and a lazy generator in a refined branch
Refined(P:pair(a,b), H:cell where a:type, b:type)<transacts>:int =
    var V:int = 0
    loop:
        if (A := (if (D := dup[P]) then (D.C | D.C + 1) else 0), set V += A, A = 5, break) then Print("not reached")
    loop:
        defer: Print("refined cleanup V={V} H={H.N}")
        if (D := dup[P]):
            if (X := Upto[H, 1, 9], set V += X, X > 2, break) then Print("not reached")
        break
    V
Main()<transacts>:void =
    Print("composed {Composed(3)}")
    Print("composed {Composed(9)}")
    H := cell{}
    Print("exclusive {Exclusive(H)} {H.N}")
    Print("refined {Refined(dup(int){A:=1, B:=2}, H)} {H.N}")
