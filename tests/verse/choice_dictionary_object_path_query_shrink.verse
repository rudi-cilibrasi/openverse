# set A.Data?[0] += A.RHS(): RHS empties the array first, so the old value's read fails, and the
# clause with it, before an addition that would overflow
ca:=class:
    var Data:?[]int=option{array{1}}
    RHS()<transacts>:int=block{Print("rhs");set Data=option{array{}};9223372036854775807}
cb:=class:
    var Data:?[]int=option{array{1}}
    RHS()<transacts>:int=block{Print("rhs");set Data=option{array{}};9223372036854775807}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data?[0]+=A.RHS()):0
    Print("{Rows.Length}")
