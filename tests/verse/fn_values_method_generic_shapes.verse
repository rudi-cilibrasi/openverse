box(t:type,u:type):=class:
    V:t
    Extra:u
    Same(X:t)<computes>:t=X
    Nested(X:[]t)<computes>:[]t=X
    Pair(X:t)<computes>:tuple(t,t)=(V,X)
    Size()<computes>:int=3
Run(B:box(t,u),X:t where t:type,u:type)<computes>:tuple(t,t,int)=
    F:=B.Same
    G:=B.Nested
    H:=B.Pair
    K:=B.Size
    R:=H(F(X))
    E:=G(array{X})
    (R(0),R(1),K()+E.Length)
Main():void=
    R:=Run(box(int,string){V:=7,Extra:="s"},9)
    Print("{R(0)} {R(1)} {R(2)}")
