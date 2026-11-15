# Independent count/sum or rollback oracle for heterogeneous producers (#335).
a:=class<computes>:
    N:int=1
    M(K:int)<computes><decides>:int=
        K>=0
        (N+K)|M[K-1]
b:=class<computes>:
    N:int=2
    M(K:int)<computes><decides>:int=
        K>=0
        (N+K)|M[K-1]
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),X0:=A0.M[1],A1:=Dup(a{})|Dup(b{}),X1:=A1.M[1],A2:=Dup(a{})|Dup(b{}),X2:=A2.M[1],A3:=Dup(a{})|Dup(b{}),X3:=A3.M[1]):X0+A0.N+X1+A1.N+X2+A2.N+X3+A3.N
    Print("{Rows.Length}")
    var Sum:int=0
    for(R:Rows):set Sum+=R
    Print("{Sum}")
