ca:=class{M(A:[]u,B:?u,C:u,?Z:int=3 where u:type)<computes>:int=A.Length+Z}
cb:=class{M(A:[]u,B:?u,C:u,?Z:int=4 where u:type)<computes>:int=A.Length+Z}
Main():void=
    P:=ca{}
    Q:=cb{}
    Print("{P.M((array{},false,7))}")
    Print("{Q.M((array{},false,7))}")
