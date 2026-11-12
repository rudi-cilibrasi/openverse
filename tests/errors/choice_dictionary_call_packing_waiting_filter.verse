ca:=class{M(X:int,Y:int)<computes>:int=X+Y}
cb:=class{M(X:int,Y:int)<computes>:int=X+Y}
Dup(X:t where t:type)<computes>:t=X|X
Args()<suspends>:tuple(int,int)=block{Sleep(0.1);(1,2)}
Main()<suspends>:void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),A.M(Args())):0
    Print("{Rows.Length}")
