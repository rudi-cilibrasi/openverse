# Nested return paths retain their condition bindings and saved locals.
# (Each return is in tail position, a branch of the body's last if: the
# function is <decides>, whose body is a failure context, Return.versetest:157.)
Visit(X:t,Y:t,N:int where t:type)<transacts><decides>:t =
    Print("visit {N}")
    if(N<=0):
        Print("base")
        B:=X
        return B|Y
    else if(M:=option{N-1}?,M>0):
        Print("special")
        B:=Y
        return B|Visit[Y,X,M]
    else:
        Print("tail")
        M:=N-1
        return X|Visit[Y,X,M]
Main():void =
    for(V:=Visit[1,2,2]): Print("got {V}")
    if(V:=Visit["a","b",2],V="b")then Print("first {V}")else Print("bad")
    if(V:=Visit["a","b",2],V="z")then Print("bad")else Print("none")
