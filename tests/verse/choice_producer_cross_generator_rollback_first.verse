a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
cell:=class{var N:int=0}
Main():void=
    C:=cell{}
    if(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(B.Data),block{set C.N+=1;false?})then Print("bad")else Print("failed {C.N}")
