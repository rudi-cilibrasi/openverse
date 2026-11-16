a:=class<computes>{M(V:t,?Z:t=V where t:type)<computes>:t=V|Z}
b:=class<computes>{M(V:t,?Z:t=V where t:type)<computes>:t=V|Z}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),B0:=Dup(left{})|Dup(right{}),X0:=A0.M(B0.Data)):1
    Print("{Rows.Length}")
