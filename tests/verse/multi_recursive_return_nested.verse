# Nested return paths retain their condition bindings and saved locals.
Visit(X:t,Y:t,N:int where t:type)<transacts><decides>:t =
    Print("visit {N}")
    if(N<=0):
        Print("base")
        B:=X
        return B|Y
    if(M:=option{N-1}?,M>0):
        Print("special")
        B:=Y
        return B|Visit[Y,X,M]
    Print("tail")
    M:=N-1
    return X|Visit[Y,X,M]
Main():void =
    for(V:=Visit[1,2,2]): Print("got {V}")
    if(V:=Visit["a","b",2],V="b")then Print("first {V}")else Print("bad")
    if(V:=Visit["a","b",2],V="z")then Print("bad")else Print("none")
