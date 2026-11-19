# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
Id(X:t where t:type)<computes>:t=X
box(t:type):=class:
    var V:t
    Pair(X:u where u:type):tuple(t,u)=(V,X)
Escape(B:box(a),X:b,Y:c where a:type,b:type,c:type):tuple(type{_(:b):tuple(a,b)},c)=
    F:type{_(:b):tuple(a,b)}=B.Pair
    Transport:type{_(:type{_(:b):tuple(a,b)},:c)<computes>:tuple(type{_(:b):tuple(a,b)},c)}=Id
    Transport(F,Y)
Main():void=
    B:=box(string){V:="before"}
    R:=Escape(B,7,3)
    set B.V="after"
    P:=R(0)(9)
    Print("{P(0)} {P(1)} {R(1)}")
