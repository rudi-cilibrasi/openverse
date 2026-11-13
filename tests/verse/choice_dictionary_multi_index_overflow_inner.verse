# set A.Data[0][0] += A.Zap(): Zap empties the inner array first, so the old value's read fails,
# and the clause with it, before an addition that would overflow
ca:=class:
    var Data:[][]int=array{array{1}}
    Zap()<transacts>:int=block{Print("rhs");set Data=array{array{}};9223372036854775807}
cb:=class:
    var Data:[][]int=array{array{1}}
    Zap()<transacts>:int=block{Print("rhs");set Data=array{array{}};9223372036854775807}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),V:=set A.Data[0][0]+=A.Zap()):V
    Print("{Rows.Length}")
