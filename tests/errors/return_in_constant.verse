# expect: return is not allowed in a constant's value (of M.X), which is in no function
M := module:
    X<public>:int = if (true?) then 1 else return 2
Main():void = Print("{M.X}")
