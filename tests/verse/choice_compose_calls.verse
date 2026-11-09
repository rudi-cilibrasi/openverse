# a function with several values whose body is a choice of calls of others: their values in order (#283)
A():int = 1 | 2
B():int = 10 | 20
C():int = A() | B()
Main():void =
    for (X := C()) { Print("{X}") }
