# expect: 4:22: unknown identifier 'X'
m := module:
    X<public>:int = 1
Main():void = Print("{X}")
