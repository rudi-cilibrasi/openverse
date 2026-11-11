cell:=class{var N:int=0}
box:=class:
    C:cell
    Same(X:t where t:type):t=
        set C.N+=1
        Print("same {C.N}")
        X
Touch(B:box):box=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Arg(C:cell,X:t where t:type):t=
    set C.N+=1
    Print("arg {C.N}")
    X
Twice(F:type{_(:t):t},X:t where t:type):t=F(X)|F(X)
Run(B:box,X:t where t:type):int=
    if(V:=Twice(Touch(B).Same,Arg(B.C,X)),false?)then Print("wrong")else Print("miss {B.C.N}")
    R:=for(V:=Twice(Touch(B).Same,Arg(B.C,X))):Print("value {B.C.N}")
    R.Length
Main():void=
    C:=cell{}
    R:=Run(box{C:=C},7)
    Print("result {R} {C.N}")
