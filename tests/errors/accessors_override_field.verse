# expect: d cannot override X, a field with accessors of c
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
d := class(c):
    var X<override>:int = 7
Main():void = {}
