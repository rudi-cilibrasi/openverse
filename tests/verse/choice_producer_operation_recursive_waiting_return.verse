# Preserve producer/consumer order, cleanup and storage across shared operations (#335).
a:=class:
    N:int=1
    M(K:int)<transacts><decides>:int=
        K>=0
        Print("a enter {K}")
        defer{Print("a cleanup {K}")}
        (block{Print("a yield {K}");N+K})|M[K-1]
b:=class:
    N:int=2
    M(K:int)<transacts><decides>:int=
        K>=0
        Print("b enter {K}")
        defer{Print("b cleanup {K}")}
        (block{Print("b yield {K}");N+K})|M[K-1]
Dup(V:t where t:type)<computes>:t=V|V
Use()<suspends>:int=
    for(A:=Dup(a{})|Dup(b{}),X:=A.M[1],B:=Dup(a{})|Dup(b{}),Y:=B.M[1]):
        defer{Print("body cleanup")}
        Sleep(0.001)
        Print("body {X} {Y}")
        if(X+Y>4):return X+Y
    99
Main()<suspends>:void=Print("return {Use()}")
