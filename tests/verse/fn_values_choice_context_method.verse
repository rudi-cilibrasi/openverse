Id(X:t where t:type)<computes>:t=X
box(t:type):=class:
    V:t
    Apply(F:type{_(:u)<computes>:u},X:u where u:type)<computes>:u=F(X)
Run(B:box(t),X:u where t:type,u:type)<computes>:u=B.Apply(Id,X)
Main():void=Print("{Run(box(string){V:="tag"},7)}")
