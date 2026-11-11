box(t:type):=class:
    V:t
    Same(X:u where u:type)<computes>:u=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Run(B:box(a),X:b where a:type,b:type)<computes>:b=Apply(B.Same,X)
Main():void=
    B:=box(string){V:="tag"}
    Print("{Run(B,7)}")
    Print("{Apply(B.Same,9)}")
