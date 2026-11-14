# expect: 'M.A' is defined twice (only functions can be overloaded)
# (a module's parts are one scope)
M<public> := module:
    A<public>:int = 42
M<public> := module:
    A<public>:int = 43
Main():void = {}
