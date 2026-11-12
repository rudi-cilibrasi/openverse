Map(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
base:=class:
    Same(X:t where t:type)<computes>:t=X
child:=class(base):
    Same(X:int,Y:int,?Tag:logic)<computes>:int=X+Y
Run(B:base,X:t where t:type)<computes>:t=Map(B.Same,X)
Main():void=Print("{Run(child{},7)}")
