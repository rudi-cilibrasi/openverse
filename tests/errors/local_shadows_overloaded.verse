# expect: 'f' is already the name of a function or constant
f():void = {}
f(X:int):void = {}
G():int =
    f := 1
    f
Main():void = {}
