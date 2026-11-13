# expect: @deprecated is on an expression or a local definition
F(X:int):int =
    @deprecated
    Y := X
    Y
Main():void = {}
