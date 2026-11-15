# expect: Sleep suspends, and a failure context
a:=class<computes>{M()<computes>:int=1|2}
b:=class<computes>{M()<computes>:int=3|4}
Dup(V:t where t:type)<computes>:t=V|V
Main()<suspends>:void=
    if(Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M()):block{Sleep(0.001);X}):Print("{Rows.Length}")
