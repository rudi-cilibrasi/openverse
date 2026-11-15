# expect: this expression can fail, but it is not in a failure context
a:=class<computes>:
    N:int=1
    M()<computes>:int=N|N+10
b:=class<computes>:
    N:int=2
    M()<computes>:int=N|N+10
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),X0:=A0.M()):false?
