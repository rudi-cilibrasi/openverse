# expect: field 'F' of class i9 is not a var
i9 := interface:
    F:int = 1
i1 := interface:
    var P:i9
c := class:
    var O:?i1 = false
Main():void =
    X := c{}
    if (set X.O?.P.F = 1) then Print("set") else Print("empty")
    if (set X.O?.P.F += "s") then Print("set") else Print("empty")
