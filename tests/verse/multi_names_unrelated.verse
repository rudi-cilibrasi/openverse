# a generator using a top-level name that an unrelated class's field also has: taken lazily, as no consumer has that field in scope (#283)
Limit:int = 3
Step(N:int)<computes>:int = N + 1
thing := class:
    Limit:int = 10
    Step:int = 2
Upto(A:int)<computes><decides>:int =
    A <= Limit
    A | Upto[Step(A)]
Main():void =
    for (X := Upto[1]) { Print("{X}") }
    Print("{thing{}.Limit}")
