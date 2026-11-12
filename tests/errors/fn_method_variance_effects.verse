# expect: expected type
box(t:type):=class:
    var V:t
    Pair()<reads>:tuple(t,int)=(V,7)
Run(B:box(t) where t:type)<computes>:void=
    F:type{_()<computes>:tuple(t,rational)}=B.Pair
Main():void=Run(box(string){V:="tag"})
