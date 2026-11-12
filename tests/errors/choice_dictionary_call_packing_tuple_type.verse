ca:=class{M(X:int,Y:int)<computes>:int=X+Y}
cb:=class{M(X:int,Y:int)<computes>:int=X+Y}
Dup(X:t where t:type)<computes>:t=X|X
Args()<computes>:tuple(int,string)=(1,"bad")
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):A.M(Args())
    Print("{Rows.Length}")
