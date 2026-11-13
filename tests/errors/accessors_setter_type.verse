# expect: its setter is SetX(:accessor, :sub):void, which c does not have
sup := class {}
sub := class(sup) {}
c := class:
    var X<getter(GetX)><setter(SetX)>:sub = external{}
    GetX(:accessor):sub = sub{}
    SetX(:accessor, V:sup):void = {}
Main():void = {}
