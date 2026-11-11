# expect: generic method of
box:=class:
    Same(X:t where t:type):t=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Same,7)}")
