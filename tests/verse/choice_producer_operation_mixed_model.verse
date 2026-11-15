# Independent count/sum or rollback oracle for heterogeneous producers (#335).
a:=class<computes>:
    N:int=1
    M()<computes>:int=N|N+10
b:=class<computes>:
    N:int=2
    M()<computes>:int=N
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),X0:=A0.M(),A1:=Dup(a{})|Dup(b{}),X1:=A1.M(),A2:=Dup(a{})|Dup(b{}),X2:=A2.M(),A3:=Dup(a{})|Dup(b{}),X3:=A3.M()):X0+A0.N+X1+A1.N+X2+A2.N+X3+A3.N
    Print("{Rows.Length}")
    var Sum:int=0
    for(R:Rows):set Sum+=R
    Print("{Sum}")
