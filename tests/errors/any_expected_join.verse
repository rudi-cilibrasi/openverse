# expect: 3:12: the branches have different types: int and string
Main():void =
    X:int = if (true?) then 1 else "a"
