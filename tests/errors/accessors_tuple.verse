# expect: a field with accessors cannot be of a tuple type, tuple(string, float)
c := class:
    var X<getter(GetX)><setter(SetX)>:tuple(string, float) = external{}
    GetX(:accessor):tuple(string, float) = ("", 0.0)
    SetX(:accessor, V:tuple(string, float)):void = {}
Main():void = {}
