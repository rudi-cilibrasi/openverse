# expect: expected type{_(:t)<computes>:t}, found type{_(?X:int = …)<computes>:int}
# (a value of Same takes no positional argument, #503)
box:=class:
    Same(?X:int=7)<computes>:int=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Same,7)}")
