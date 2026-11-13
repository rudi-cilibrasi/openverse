# expect: its getter is GetX(:accessor):int, which c does not have
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    GetX(:accessor):logic = false
    SetX(:accessor, V:int):void = {}
Main():void = {}
