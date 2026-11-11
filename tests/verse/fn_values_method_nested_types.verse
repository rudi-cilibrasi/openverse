wrap(t:type):=struct{V:t}
box(t:type,u:type):=class:
    V:t
    Extra:u
    Same(X:t):t=X
    Array(X:[]t):[]t=X
    Record(X:wrap(t)):wrap(t)=X
    Mapping(X:[string]t):[string]t=X
    Function(X:type{_(:t):t}):type{_(:t):t}=X
Run(B:box(a,b),X:a where a:type,b:type):tuple(a,a,a,int)=
    Id:=B.Same
    H:=B.Function
    F:=H(Id)
    A:=B.Array
    R:=B.Record
    M:=B.Mapping
    E:=A(array{})
    Z:=R(wrap(a){V:=X})
    K:=M(map{"key"=>X})
    (F(X),Z.V,K["key"] or X,E.Length)
Main():void=
    R:=Run(box(int,string){V:=7,Extra:="s"},9)
    Print("{R(0)} {R(1)} {R(2)} {R(3)}")
