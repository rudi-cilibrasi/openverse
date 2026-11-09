# expect: 4:15: F takes 1 argument(s), found 2
F(X:int):int = X | X * 2
Main():void =
    for (V := F(1, 100)) { Print("{V}") }
