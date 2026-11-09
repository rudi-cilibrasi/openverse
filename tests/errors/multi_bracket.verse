# expect: 4:19: Twice is not <decides>: call it with Twice(…)
Twice(X:int):int = X | X * 2
Main():void =
    for (V := Twice[3]) { Print("{V}") }
