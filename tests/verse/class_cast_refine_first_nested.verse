pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 4
Lazy(N:int)<computes>:int =
    if (N > 0) then (N | Lazy(N - 1)) else 0
Use(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):void =
    if (V := if (D := dup[P]) then Lazy(D.C) else 0, V < 3):
        Print("lazy {V}")
    if (V := if (D := dup[P], K := 1 | 2, K > 1) then (D.C + K | D.C) else 0, V > 4):
        Print("more choice {V}")
    if (V := if (X := P, D := dup[X]) then (D.C | D.C + 1) else 0, V > 4):
        Print("later {V}")
    if (V := if (D := dup[P]) then (if (E := dup[Q]) then (D.C + E.C | D.C) else 0) else 0, V > 4):
        Print("nested {V}")
    if (V := (if (D := dup[P]) then (D.C | D.C + 1) else 0) | 99, V > 10):
        Print("composed {V}")
Main():void =
    Match := dup(int){A := 1, B := 2}
    Miss := pair(int, string){A := 1, B := "s"}
    Use(Match, Match)
    Use(Match, Miss)
    Use(Miss, Match)
