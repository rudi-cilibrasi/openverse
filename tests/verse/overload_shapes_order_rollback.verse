# Receiver first; tuple producer once; names as written; selected defaults.
cell := class:
    var N:int = 0
Tick(C:cell,Tag:string)<transacts>:int =
    set C.N += 1
    Print("{Tag} {C.N}")
    C.N
Pair(C:cell)<transacts>:tuple(int,string) =
    Tick(C,"tuple")
    (10,"value")
box := class:
    C:cell
    M(X:tuple(int,string),?A:int,?B:int,?D:int=Tick(C,"default"))<transacts>:int =
        Print("body {X(0)} {A} {B} {D}")
        X(0)+A+B+D
    M(X:[]int,?A:int,?B:int,?D:int=Tick(C,"wrong-default"))<transacts>:int =
        Print("wrong-body")
        0
Touch(B:box)<transacts>:box =
    Tick(B.C,"receiver")
    B
Main():void =
    C := cell{}
    B := box{C:=C}
    if(R:=Touch(B).M(Pair(C),?B:=Tick(C,"B"),?A:=Tick(C,"A")),Print("suffix"),false?):
        Print("wrong")
    else:
        Print("reject {C.N}")
    R := Touch(B).M(Pair(C),?B:=Tick(C,"B"),?A:=Tick(C,"A"))
    Print("result {R} {C.N}")
