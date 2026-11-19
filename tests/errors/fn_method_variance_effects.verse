# expect: expected type
# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
box(t:type):=class:
    var V:t
    Pair()<reads>:tuple(t,int)=(V,7)
Run(B:box(t) where t:type)<computes>:void=
    F:type{_()<computes>:tuple(t,rational)}=B.Pair
Main():void=Run(box(string){V:="tag"})
