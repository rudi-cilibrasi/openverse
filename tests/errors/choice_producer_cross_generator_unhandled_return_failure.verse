# expect: this expression can fail, but it is not in a failure context
a:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
b:=class<computes>{M(V:t where t:type)<computes>:t=V|V}
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Run():int=
    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(B.Data)):
        1=2
        if(true?):return 3
        1
    Rows.Length
Main():void=Print("{Run()}")
