# expect: field 'X' of c has accessors and no default external{}: a construction gives it a value
c := class:
    var X<getter(GetX)><setter(SetX)>:int
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
Main():void =
    Y := c{}
