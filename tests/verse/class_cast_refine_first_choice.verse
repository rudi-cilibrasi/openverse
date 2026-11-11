# Class casts keep the chosen branch's refinement through first-success search.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Read(P:pair(a, b), H:counter where a:type, b:type)<transacts>:pair(a, b) =
    set H.N += 1
    P
Touch(H:counter, Amount:int, Value:int)<transacts>:int =
    set H.N += Amount
    Value
Values(N:int)<computes>:int = N | N + 1
Simple(P:pair(a, b) where a:type, b:type):void =
    if (V := if (D := dup[P]) then (D.C | D.C + 1) else 0, V > 4):
        Print("simple {V}")
    else:
        Print("simple missed")
    X := option{V := if (D := dup[P]) then (D.C | D.C + 1) else 0; V > 4; V}
    if (V := X?) then Print("option {V}") else Print("option missed")
Effects(P:pair(a, b) where a:type, b:type)<transacts>:void =
    H := counter{}
    if (V := if (D := dup[Read(P, H)]):
        set H.N += 100
        Touch(H, 10, D.C) | Touch(H, 20, D.C + 1)
    else:
        Touch(H, 50, 0)
    , V > 4):
        Print("effects {V} {H.N}")
    else:
        Print("effects missed {H.N}")
NoFallback(P:pair(a, b) where a:type, b:type)<transacts>:void =
    H := counter{}
    A := array{1}
    if (V := if (D := dup[Read(P, H)]) then (A[D.C] | A[D.C + 1]) else Touch(H, 50, 99)):
        Print("fallback {V} {H.N}")
    else:
        Print("no fallback {H.N}")
More(P:pair(a, b), Threshold:int where a:type, b:type):void =
    if (V := if (D := dup[P], K := D.C, K > Threshold) then (K | K + 1) else 0, V > 4):
        Print("more {V}")
    else:
        Print("more missed")
    if (V := if (false?) then -1 else if (D := dup[P]) then Values(D.C) else 0, V > 4):
        Print("chain {V}")
    else:
        Print("chain missed")
Join(P:pair(a, b) where a:type, b:type):void =
    if (V := if (D := dup[P]) then (false | option{D.C}) else option{8}, N := V?):
        Print("join {N}")
Cleanup(P:pair(a, b) where a:type, b:type)<transacts>:void =
    H := counter{}
    if (V := if (D := dup[P]):
        defer: set H.N += 100
        D.C | D.C + 1
    else:
        0
    , V > 4, H.N = 100):
        Print("cleanup {V} {H.N}")
    else:
        Print("cleanup missed {H.N}")
Prior(P:pair(a, b), Q:pair(a, b) where a:type, b:type):void =
    if (X := P | Q, V := if (D := dup[X]) then (D.C | D.C + 1) else 0, V = 0):
        Print("prior choice {V}")
LocalState(P:pair(a, b) where a:type, b:type):void =
    var Total:int = 0
    if (V := if (D := dup[P]) then (D.C | D.C + 1) else 0, set Total += V, W := Total, V > 4):
        Print("local {Total} {W}")
    else:
        Print("local missed {Total}")
    if (set Total = if (D := dup[P]) then (D.C | D.C + 1) else 0, Total > 4):
        Print("set {Total}")
    else:
        Print("set missed {Total}")
Sequential(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<transacts>:void =
    H := counter{}
    var Total:int = 0
    if (V := if (D := dup[P]) then (Touch(H, 1, D.C) | Touch(H, 2, D.C + 1)) else 0,
        set Total += V,
        W := if (E := dup[Q]) then (Touch(H, 10, V + E.C) | Touch(H, 20, V + E.C + 1)) else V,
        set Total += W,
        W > 8):
        Print("sequential {V} {W} {Total} {H.N}")
    else:
        Print("sequential missed {Total} {H.N}")
Main()<transacts>:void =
    Match := dup(int){A := 1, B := 2}
    Miss := pair(int, string){A := 1, B := "s"}
    Simple(Match)
    Simple(Miss)
    Effects(Match)
    Effects(Miss)
    NoFallback(Match)
    NoFallback(Miss)
    More(Match, 0)
    More(Match, 9)
    More(Miss, 0)
    Join(Match)
    Join(Miss)
    Cleanup(Match)
    Cleanup(Miss)
    Prior(Match, pair(int, int){A := 1, B := 2})
    LocalState(Match)
    LocalState(Miss)
    Sequential(Match, Match)
    Sequential(Match, Miss)
