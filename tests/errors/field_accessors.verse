# expect: <getter(GetX)>: X is a field with accessors
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):int = 0
    SetX(:accessor, N:int):void = {}
Main():void = {}
