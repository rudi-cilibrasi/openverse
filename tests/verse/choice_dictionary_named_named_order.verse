box:=class:
    var K:int=0
Mark(B:box,Tag:string,N:int)<transacts>:int=
    Print(Tag)
    set B.K += N
    B.K
ca:=class:
    M(B:box,?X:int=Mark(B,"default x a",10),?Y:int=Mark(B,"default y a",100))<transacts>:int=X+Y
cb:=class:
    M(B:box,?X:int=Mark(B,"default x b",20),?Y:int=Mark(B,"default y b",200))<transacts>:int=X+Y
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    B:=box{}
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        V:=A.M(B,?Y:=Mark(B,"given y",1))
        Print("body {V} {B.K}")
        W:=A.M(B,?Y:=Mark(B,"given second y",2),?X:=Mark(B,"given second x",3))
        Print("second {W} {B.K}")
        V+W
    Print("done {Rows.Length} {B.K}")
