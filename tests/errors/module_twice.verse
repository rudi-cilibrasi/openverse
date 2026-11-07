# expect: 2:0: m is defined twice (a module and a definition)
m := module:
    X<public>:int = 1
m():int = 1
Main():void = Print("x")
