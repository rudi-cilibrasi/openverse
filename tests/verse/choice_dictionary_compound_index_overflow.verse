# set A.Data[0] += RHS() at the longest int: the overflow error, in the first
# alternative, after its right side (#724: on 64-bit ints, at 2^63 - 1)
# The longest int, 2^(2^20) - 1: one more is the overflow error (#724).
MaxInt()<computes>:int =
    var H:int = 2
    for (I := 1..19):
        set H *= H
    (H - 1) * (H + 1)
ca:=class{var Data:[]int=array{0}}
cb:=class{var Data:[]int=array{0}}
Dup(X:t where t:type)<computes>:t=X|X
RHS()<transacts>:int=block{Print("rhs");1}
Main():void=
    M:=MaxInt()
    Rows:=for(A:=(Dup(ca{Data:=array{M}})|Dup(cb{Data:=array{M}})),set A.Data[0]+=RHS()):0
    Print("{Rows.Length}")
