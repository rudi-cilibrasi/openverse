# expect: its getter is a method of c or of a class or interface above it, and GetX is a function, not a method
GetX(:accessor):int = 0
SetX(:accessor, V:int):void = {}
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
Main():void = {}
