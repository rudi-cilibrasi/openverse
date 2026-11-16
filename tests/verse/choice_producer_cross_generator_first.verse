a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Main():void=
    if(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(B.Data)):Print("found")
