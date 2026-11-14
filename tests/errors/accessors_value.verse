# expect: it has no storage, so no value of its own: write = external{} or nothing
c := class:
    var X<getter(GetX)><setter(SetX)>:int = 4
    GetX(:accessor):int = 0
    SetX(:accessor, V:int):void = {}
Main():void = {}
