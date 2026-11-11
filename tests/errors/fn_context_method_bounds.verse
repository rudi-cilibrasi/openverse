# expect: 'Same' is a generic method of box
box:=class:
    Same(X:t where t:subtype(comparable))<computes>:t=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Run(B:box,X:t where t:type)<computes>:t=Apply(B.Same,X)
Main():void={}
