# compositions nested through functions, in a for and an if (#283)
A():int = 1 | 2
B():int = 10 | 20
C():int = A() | B()
D():int = C() | 100
Main():void =
    for (X := D()) { Print("{X}") }
    if (X := D(), X > 15, Y := A() | B(), X + Y > 112) then Print("{X} {Y}")
