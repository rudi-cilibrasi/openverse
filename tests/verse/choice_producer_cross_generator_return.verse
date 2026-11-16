a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Run():int=
    var N:int=0
    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(B.Data)):
        set N+=1
        if(N=3):return N
        1
    999
Main():void=Print("{Run()}")
