# expect: <final> is not allowed on a module's function
M := module:
    F<final>():int = 1
Main():void = {}
