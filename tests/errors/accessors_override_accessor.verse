# expect: d cannot override GetX, an accessor of c's field X
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
d := class(c):
    GetX<override>(:accessor):int = 1
Main():void = {}
