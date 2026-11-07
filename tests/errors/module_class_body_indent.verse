# expect: 4:4: expected the indented body of class M.c
M := module:
    c<public> := class:
    X:int = 1
Main():void = Print("x")
