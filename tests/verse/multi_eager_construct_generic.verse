# Contextual instances and inherited defaults keep their type and home scope.
base(t:type) := class:
    E:[]t = block{ Empty:[]t=Concatenate(); Empty }
    D:int = block{ N := 7; N }
    V:t
    K:int
    T:int = 1+2
pack(u:type) := class(base(u)) {}
Build(X:t,N:int where t:type)<computes>:pack(t) =
    if (N>0) then (pack{K:=N*10|N*10+1,V:=X} | Build(X,N-1)) else pack{K:=0,V:=X}
Show(X:t where t:type)<transacts>:void =
    N := 99
    Ps := for (P := Build(X,2)):
        Print("value {P.K} {P.D} {P.E.Length} {P.T} {N}")
        P
    for (P : Ps): Print("saved {P.K} {P.D}")
Main()<transacts>:void =
    Show(7)
    Show("s")
