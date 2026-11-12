ca:=class:
    var Data:[][]int=array{array{1}}
    Zap()<transacts>:int=block{Print("rhs");set Data=array{array{}};9223372036854775807}
cb:=class:
    var Data:[][]int=array{array{1}}
    Zap()<transacts>:int=block{Print("rhs");set Data=array{array{}};9223372036854775807}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data[0][0]+=(A.Zap()|A.Zap())):0
    Print("{Rows.Length}")
