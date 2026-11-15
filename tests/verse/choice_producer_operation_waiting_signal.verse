a:=class<computes>{M()<computes>:int=1|2}
b:=class<computes>{M()<computes>:int=3|4}
Dup(V:t where t:type)<computes>:t=V|V
Main()<suspends>:void=
    E:=event(int){}
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):
        Sleep(0.001)
        E.Signal(X+Y)
    Print("{Rows.Length}")
