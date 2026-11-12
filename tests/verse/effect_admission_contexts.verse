cell := class:
    var N:int = 0
Tick(C:cell,Tag:string)<reads><writes>:int =
    set C.N += 1
    Print("{Tag} {C.N}")
    C.N
Use(C:cell,X:t where t:type)<reads><writes>:int = Tick(C,"generic")
i := interface:
    Bump(X:int)<reads><writes>:int
box(t:type) := class(i):
    C:cell
    Token:t
    Bump<override>(X:int)<reads><writes>:int = X+Tick(C,"body")
    Pick(?X:int=Tick(C,"default"))<reads><writes>:int = X
Apply(F:type{_(:int)<reads><writes>:int},X:int)<reads><writes>:int = F(X)
root(t:type) := class{}
leaf := class(root(int)):
    C:cell
Opened(P:root(t) where t:type)<reads><writes>:int =
    if(D:=leaf[P])then Tick(D.C,"opened")else -1
Main():void =
    C := cell{}
    B := box(string){C:=C,Token:="token"}
    F:type{_(:int)<reads><writes>:int} = B.Bump
    if(R:=Apply(F,Tick(C,"argument")),Print("suffix"),false?):
        Print("wrong")
    else:
        Print("reject {C.N}")
    R := Apply(F,Tick(C,"argument"))
    Print("callback {R} {C.N}")
    Print("default-result {B.Pick()} {C.N}")
    Print("explicit-result {B.Pick(?X:=7)} {C.N}")
    for(X:=1|2):
        Print("choice {Use(C,X)} {C.N}")
    Print("cast {Opened(leaf{C:=C})} {C.N}")
    set C.N = 10
    Print("live {F(2)} {C.N}")
