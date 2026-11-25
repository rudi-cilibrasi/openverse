# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
box(t:type):=class:
    var V:t
    Pair(X:u,Y:u where u:type):tuple(t,u,u)=(V,X,Y)
Bind(B:box(a),X:b where a:type,b:type):type{_(:tuple(b,b)):tuple(a,b,b)}=B.Pair
Main():void=
    B:=box(string){V:="before"}
    F:=Bind(B,7)
    set B.V="after"
    R:=F((9,11))
    Print("{R(0)} {R(1)} {R(2)}")
