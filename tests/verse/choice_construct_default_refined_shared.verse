pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)) {}
box(t:type) := struct { E:[]t = Concatenate(); B:int }
Two(N:int):int = N | N + 1
Keep(V:t, P:box(t) where t:type):box(t) = P
Run(P:pair(a,b) where a:type,b:type):void =
    R := for (A := (Two(0) | Two(2)), B:box(a) = if (D := dup[P]) then Keep(D.A, box{B := 1 | 2}) else box(a){B := 0}, C := (Two(0) | Two(2))):
        B.B + B.E.Length
    Print("count {R.Length}")
Main():void =
    Run(dup(int){A:=1,B:=2})
    Run(pair(int,string){A:=1,B:="s"})
