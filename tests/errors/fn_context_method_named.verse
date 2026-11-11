# expect: named parameters
box:=class:
    Same(?X:int=7)<computes>:int=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Same,7)}")
