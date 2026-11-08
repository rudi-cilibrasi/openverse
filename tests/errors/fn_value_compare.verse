# expect: is a function type (Book of Verse ch. 4: functions are not comparable)
D(X:int):int = X
Main():void =
    F:int->int = D
    G:int->int = D
    if (F = G) then Print("eq")
