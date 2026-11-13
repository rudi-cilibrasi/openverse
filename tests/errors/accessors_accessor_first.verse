# expect: SetX is the setter of X, so it takes the accessor first
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
    SetX(V:float):void = {}
Main():void = {}
