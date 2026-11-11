# expect: overloaded method
box:=class:
    Same(X:int)<computes>:int=X
    Same(X:string)<computes>:string=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Same,7)}")
