# A helper's written types use the aliases of the refining cast that owns it.
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)) {}
Nat(N:int)<transacts><decides>:int =
    Print("cast search {N}")
    N | Nat[N+1]
Echo(X:t,N:int where t:type)<transacts><decides>:t =
    N <= 2
    Print("echo {N}")
    X | Echo[X,N+1]
Refined(P:pair(a,b) where a:type,b:type)<transacts>:?b =
    if (D := dup[P]):
        var Current:b = D.B
        if (Y:a = Echo[D.A,0], I := Nat[0], set Current = Y, E:[]a = array{Current}, I > 1):
            option{Current}
        else:
            false
    else:
        false
Main()<transacts>:void =
    if (X := Refined(dup(int){A:=1,B:=2})?) then Print("refined {X}")
    if (X := Refined(dup(string){A:="a",B:="b"})?) then Print("refined {X}")
    if (Refined(pair(int,string){A:=9,B:="miss"})?) then Print("unexpected")
