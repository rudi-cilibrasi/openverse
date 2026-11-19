# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
box(t:type):=class:
    var V:t
    Pair(X:int)<reads>:tuple(t,int)=(V,X)
Bind(B:box(t) where t:type)<computes>:type{_(:int)<reads>:tuple(t,rational)}=B.Pair
Main():void=
    B:=box(string){V:="before"}
    F:=Bind(B)
    set B.V="after"
    R:=F(9)
    Print("{R(0)} {Floor(R(1))}")
