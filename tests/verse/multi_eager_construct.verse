# Eager recursion lifts fields in declaration order, including nested calls.
box := struct:
    D:int = 1+2
    V:int
pair := struct:
    A:int
    D:int = block{ N := 7; N }
    B:int
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Pick(N:int)<computes>:int = N | N+1
Nested(N:int,?Step:int=2)<computes>:int =
    if (N>0) then (pair{B:=Pick(N+10),A:=Pick(N)}.A | Nested(box{V:=N|N+1}.V-Step)) else 0
Main():void =
    for (V := R(2)): Print("plain {V}")
    for (V := Nested(1)): Print("nested {V}")
    if (V := R(2), V > 0) then Print("first {V}")
    if (V := R(2), V > 9) then Print("unexpected") else Print("none")
