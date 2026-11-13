# expect: a struct's field cannot have accessors, only a class's or an interface's
s := struct:
    var X<getter(G)><setter(S)>:int = external{}
Main():void = {}
