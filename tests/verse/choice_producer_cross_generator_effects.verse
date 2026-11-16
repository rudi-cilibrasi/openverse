a:=class:
    M(V:t where t:type):t=
        Print("a enter")
        defer{Print("a cleanup")}
        (block{Print("a yield1");V})|(block{Print("a yield2");V})
b:=class:
    M(V:t where t:type):t=
        Print("b enter")
        defer{Print("b cleanup")}
        (block{Print("b yield1");V})|(block{Print("b yield2");V})
left:=class<computes>{Data:int=1}
right:=class<computes>{Data:string="s"}
Dup(V:t where t:type)<computes>:t=V|V
Arg(V:t where t:type):t=
    Print("argument")
    V
Main():void=
    Rows:=for(A:=Dup(a{})|Dup(b{}),B:=Dup(left{})|Dup(right{}),X:=A.M(Arg(B.Data))):
        Print("body")
        1
    Print("rows {Rows.Length}")
