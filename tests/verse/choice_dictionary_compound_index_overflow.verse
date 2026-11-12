ca:=class{var Data:[]int=array{9223372036854775807}}
cb:=class{var Data:[]int=array{9223372036854775807}}
Dup(X:t where t:type)<computes>:t=X|X
RHS()<transacts>:int=block{Print("rhs");1}
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data[0]+=RHS()):0
    Print("{Rows.Length}")
