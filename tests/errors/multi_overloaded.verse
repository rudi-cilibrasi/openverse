# expect: has several values and is overloaded
F(S:string):string = S
F(X:int):int = X | X + 1
Main():void =
    for (V := F(1)) { Print("{V}") }
