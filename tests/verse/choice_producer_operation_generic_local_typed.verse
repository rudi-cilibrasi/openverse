# Preserve later-clause generic instance typing and source annotation (#335).
a:=class<computes>:
    N:int=1
    M(V:t where t:type)<computes>:t=V|V
b:=class<computes>:
    N:int=2
    M(V:t where t:type)<computes>:t=V|V
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),Z0:int=A0.N+1,X0:=A0.M(Z0),A1:=Dup(a{})|Dup(b{}),Z1:int=A1.N+1,X1:=A1.M(Z1)):X0+A0.N+X1+A1.N
    Print("{Rows.Length}")
    var Sum:int=0
    for(R:Rows):set Sum+=R
    Print("{Sum}")
