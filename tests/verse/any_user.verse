# a program's own function named any is its own; unrelated classes join at any (#138 review)
any(X:int):void = Print("called {X}")
Main():void =
    any(1)
    Print("done")
