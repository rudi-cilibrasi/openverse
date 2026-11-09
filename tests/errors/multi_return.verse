# expect: 2:0: Early has several values and a return
Early(X:int):int =
    if (X > 5) then return 0
    X | X + 1
Main():void =
    for (V := Early(1)) { Print("{V}") }
