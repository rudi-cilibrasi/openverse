a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
cell:=class{var N:int=0}
Use(C:cell)<decides>:void=
    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(B.Data)):
        set C.N+=1
        C.N<2
        1
    {}
Main():void=
    C:=cell{}
    if(Use[C])then Print("bad")else Print("failed {C.N}")
