# a set through an option of an interface no class implements (104):
# the query fails first, so the set fails; it never reaches the unreachable write

i1 := interface:
    var F2:int = 15
c := class:
    var O:?i1 = false
Main():void =
    X := c{}
    if (set X.O?.F2 += 7) then Print("set") else Print("empty")
    if (set X.O?.F2 = 7) then Print("set") else Print("empty")
    if (Y := X.O?.F2) then Print("read") else Print("empty")
