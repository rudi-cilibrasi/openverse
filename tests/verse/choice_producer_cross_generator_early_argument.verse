a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Arg(V:t where t:type):t=
    return V
Main():void=
    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(Arg(B.Data))):1
    Print("{Rows.Length}")
