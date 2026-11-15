# A refining cast branch may break out of its enclosing loop while its normal result is inferred.
# Each line compares inference with an explicit int annotation.
box(t:type) := class:
    V:t
ibox := class(box(int)):
    C:int = 0
Inferred(P:box(t) where t:type):int =
    var N:int = 0
    loop:
        X := if (D := ibox[P]):
            if (D.C > 0) then break
            D.V
        else:
            9
        set N = X
        break
    N
Explicit(P:box(t) where t:type):int =
    var N:int = 0
    loop:
        X:int = if (D := ibox[P]):
            if (D.C > 0) then break
            D.V
        else:
            9
        set N = X
        break
    N
Main():void =
    Print("{Inferred(ibox{V:=7,C:=1})} {Explicit(ibox{V:=7,C:=1})}")
    Print("{Inferred(ibox{V:=7,C:=0})} {Explicit(ibox{V:=7,C:=0})}")
    Print("{Inferred(box(string){V:="a"})} {Explicit(box(string){V:="a"})}")
