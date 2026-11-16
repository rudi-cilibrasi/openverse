a:=class<computes>{M(V:t,N:int where t:type)<computes><decides>:t=block{N>=0;V|M[V,N-1]}}
b:=class<computes>{M(V:t,N:int where t:type)<computes><decides>:t=block{N>=0;V|M[V,N-1]}}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),B0:=Dup(left{})|Dup(right{}),X0:=A0.M[B0.Data,1]):1
    Print("{Rows.Length}")
