ca:=class:
    var Data:[]?int=array{option{1}}
    RHS()<transacts>:int=block{Print("rhs");set Data=array{false};9223372036854775807}
cb:=class:
    var Data:[]?int=array{option{1}}
    RHS()<transacts>:int=block{Print("rhs");set Data=array{false};9223372036854775807}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data[0]?+=A.RHS()):0
    Print("{Rows.Length}")
