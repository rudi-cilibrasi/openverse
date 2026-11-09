# expect: 4:12: Two has several values, so a call of it must be in a failure context that takes them
Two():int = 1 | 2
Main():void =
    X := Two()
    Print("{X}")
