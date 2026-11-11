# Generic values, mutable copy-outs, written witnesses and recursive groups.
meter := class:
    var N:int = 0
cell(t:type) := class:
    var Value:t
    var Hits:int = 0
Nat(H:meter,N:int)<transacts><decides>:int =
    N <= 3
    set H.N += 1
    Print("nat {N} {H.N}")
    N | Nat[H,N+1]
Even(H:meter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 1
    Print("even {N} {H.N}")
    N | Odd[H,N-1]
Odd(H:meter,N:int)<transacts><decides>:int =
    N >= 0
    set H.N += 2
    Print("odd {N} {H.N}")
    N | Even[H,N-1]
Walk(H:meter,A:[]t,I:int where t:type)<transacts><decides>:t =
    I < A.Length
    set H.N += 1
    Print("walk {I} {H.N}")
    A[I] | Walk[H,A,I+1]
Search(Start:t,End:t,C:cell(t),H:meter,Cut:int where t:type)<transacts>:?t =
    var Current:t = Start
    var Total:int = 0
    R := if (I := Nat[H,0], set Total += I, set Current = End,
        set C.Value = Current, set C.Hits += 1, Print("try {I} {Total} {C.Hits}"), I >= Cut):
        Print("found {I} {Total} {C.Hits}")
        option{Current}
    else:
        Print("none {Total} {C.Hits}")
        false
    Print("state {Total} {C.Hits} {H.N}")
    R
Values(A:[]t,H:meter where t:type)<transacts>:?t =
    if (X := Walk[H,A,0], E:[]t = array{X}, E.Length > 0) then option{X} else false
Witness(Unused:t,H:meter where t:type)<transacts>:int =
    if (I := Nat[H,0], block{ E:[]t = array{}; E.Length = 0 }, I > 1) then I else -1
GroupWitness(Unused:t,H:meter where t:type)<transacts>:int =
    if (I := Even[H,3], block{ E:[]t = array{}; E.Length = 0 }, I < 1) then I else -1
Group(X:t,Y:t,H:meter where t:type)<transacts>:?t =
    var Current:t = X
    if (I := Even[H,3], set Current = Y, I < 1) then option{Current} else false
Main()<transacts>:void =
    H := meter{}
    C := cell(string){Value:="initial"}
    if (X := Search("a","b",C,H,2)?) then Print("result {X}")
    Print("cell {C.Value} {C.Hits}")
    R := Search("c","d",C,H,9)
    if (R?) then Print("unexpected") else Print("rejected")
    Print("cell {C.Value} {C.Hits}")
    D := cell(int){Value:=7}
    if (X := Search(8,9,D,H,1)?) then Print("result {X}")
    Print("cell {D.Value} {D.Hits}")
    if (X := Values(array{"first","second"},H)?) then Print(X)
    if (X := Values(array{4,5},H)?) then Print("{X}")
    Print("witness {Witness("s",H)} {Witness(1,H)}")
    Print("group witness {GroupWitness("s",H)} {GroupWitness(1,H)}")
    if (X := Group("old","new",H)?) then Print(X)
    if (X := Group(10,20,H)?) then Print("{X}")
    Print("visits {H.N}")
