# expect: expected type
box(t:type):=class:
    V:t
    Same(X:t)<computes>:t=X
Run(B:box(t) where t:type)<computes>:void=
    F:type{_(:int)<computes>:rational}=B.Same
Main():void=Run(box(string){V:="tag"})
