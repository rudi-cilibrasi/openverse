# expect: 5:9: m is a module, not a value
m := module:
    X<public>:int = 2
Main():void =
    Y := m
    Print("x")
