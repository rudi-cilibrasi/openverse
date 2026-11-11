# Generic/default bindings and written witnesses survive the outer lift.
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
Repeat(X:t,N:int where t:type)<computes><decides>:t =
    N >= 0
    X | Repeat[X,N-1]
Pick(X:t,?Y:t=X where t:type)<computes>:t = X | Y
Typed(X:t,P:pair(a,b) where t:type,a:type,b:type):[][]t =
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        for (Y := Repeat[X,1], Z := Pick(Y)):
            Empty:[]t = array{}
            Z
First(X:t,P:pair(a,b) where t:type,a:type,b:type):t =
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        if (Y := Repeat[X,1]):
            return Y
    X
Written(Unused:t,P:pair(a,b) where t:type,a:type,b:type):int =
    R := for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        for (L := Repeat[V,1]):
            Empty:[]t = array{}
            Empty.Length
    R.Length
box(t:type) := class:
    Value:t
    Run(P:pair(a,b) where a:type,b:type):[][]t =
        for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
            for (Y := Repeat[Value,0], Z := Pick(Y)):
                Z
Main():void =
    P := dup(int){A:=1,B:=2}
    for (A : Typed(7,P)):
        for (V : A):
            Print("typed {V}")
    for (A : Typed("s",P)):
        for (V : A):
            Print("typed {V}")
    Print("first {First(8,P)}")
    Print("first {First("t",P)}")
    B := box(string){Value:="method"}
    for (A : B.Run(P)):
        for (V : A):
            Print(V)
    Print("written {Written(9,P)}")
    Print("written {Written("w",P)}")
