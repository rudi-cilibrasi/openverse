# Defaults and contextual empty values retain generic types on recursive edges.
Repeat(X:t,N:int,?Y:t=X where t:type)<transacts><decides>:t =
    N > 0
    Print("repeat {N}")
    Y | Repeat[X,N-1]
Empty(X:?t,N:int,?Y:?t=false where t:type)<transacts><decides>:?t =
    N > 0
    Print("empty {N}")
    X | Empty[Y,N-1]
Pick(X:t,?Y:t=X where t:type)<computes>:t = X | Y
Eager(X:t,N:int,?Y:t=X where t:type)<computes>:t =
    if (N>0) then (Pick(X,?Y:=Y) | Eager(X,N-1)) else X
holder(t:type) := class:
    Value:t
    Get(N:int,?X:t=Value)<transacts><decides>:t =
        N > 0
        Print("method {N}")
        X | Get[N-1]
Main()<transacts>:void =
    for (X := Repeat["a",2,?Y:="b"]): Print(X)
    if (X := Repeat["c",2,?Y:="d"], X = "c") then Print(X)
    for (X := Repeat[1,2,?Y:=2]): Print("{X}")
    for (X := Empty[option{"s"},2]):
        if (V := X?) then Print(V) else Print("empty option")
    for (X := Eager("e",2,?Y:="f")): Print(X)
    for (X := Eager(3,2,?Y:=4)): Print("{X}")
    H := holder(string){Value:="field"}
    for (X := H.Get[2,?X:="explicit"]): Print(X)
    if (X := H.Get[2], X = "field") then Print(X)
