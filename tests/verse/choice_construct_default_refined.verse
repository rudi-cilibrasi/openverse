pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
box(t:type) := struct { E:[]t = Concatenate(); B:int }
Two(N:int):int = N | N + 1
Read(V:t, Q:box(t) where t:type):int = Q.E.Length + Q.B
Run(P:pair(a, b) where a:type, b:type):void =
    for (Q := if (D := dup[P]) then (Read(P.A, box{B := (Two(0) | Two(2))}) | Read(P.A, box{B := Two(4)})) else Read(P.A, box{B := Two(8)}), X := (Two(0) | Two(2)), X = 0):
        Print("refined {Q}")
Main():void =
    Run(dup(int){A := 1, B := 2})
    Run(pair(int, string){A := 1, B := "s"})
