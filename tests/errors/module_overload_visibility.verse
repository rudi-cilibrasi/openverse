# expect: 3:4: the overloads of M.S must all be <public> or all internal
M := module:
    S<public>(X:int):string = "i"
    S(X:string):string = "s"
Main():void = Print(M.S(1))
