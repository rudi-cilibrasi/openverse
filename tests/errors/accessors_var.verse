# expect: X is a field with accessors, so it is a var
c := class:
    X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
Main():void = {}
