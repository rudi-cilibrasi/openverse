# expect: 4:4: c.ToChar has several values, but ToChar is also the name of
# Nor a scalar's method's: 65.ToChar[] could be its call.
c := class:
    ToChar():int = 1 | 2
Main():void =
    for (V := c{}.ToChar()) { Print("{V}") }
    if (C := 65.ToChar[]) then Print("{C}")
