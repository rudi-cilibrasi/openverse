cell:=class{var N:int=0}
box(t:subtype(comparable),u:type):=class:
    var V:t
    Extra:u
    C:cell
    Same(X:t)<transacts>:t=
        set C.N+=1
        Print("same {C.N}")
        if(V=V)then V else V
    Nested(X:[]t)<transacts>:[]t=
        set C.N+=1
        Print("nested {C.N}")
        X
    Pair(X:t)<transacts>:tuple(t,t)=
        set C.N+=1
        Print("pair {C.N}")
        (V,X)
    Size()<transacts>:int=
        set C.N+=1
        Print("size {C.N}")
        29+C.N
Touch(B:box(a,b) where a:subtype(comparable),b:type)<transacts>:box(a,b)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Run(B:box(a,b),X:a where a:subtype(comparable),b:type)<transacts>:tuple(a,a,a,a,int,int)=
    F:=Touch(B).Same
    G:=B.Nested
    H:=B.Pair
    K:=B.Size
    Before:=B.V
    set B.V=X
    Y:=F(Before)
    E:=G(array{Y})
    P:=H(Before)
    S:=K()
    (Y,P(0),P(1),E[0] or Y,S,B.C.N)
Main():void=
    R:=Run(box(string,int){V:="old",Extra:=4,C:=cell{}},"new")
    Print("result {R(0)} {R(1)} {R(2)} {R(3)} {R(4)} {R(5)}")
