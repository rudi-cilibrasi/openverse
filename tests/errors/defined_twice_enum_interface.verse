# expect: 'M.A' is defined twice (only functions can be overloaded)
M := module:
    A<public> := enum{ Red, Blue }
    A<public> := interface{}
Main():void = {}
