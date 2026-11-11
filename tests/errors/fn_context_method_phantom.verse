# expect: generic method of
box:=class:
    Empty(X:int where t:type)<computes>:int=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Empty,7)}")
