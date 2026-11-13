# a generator using a top-level name that a class's field also has: computed eagerly, as inlining it would change what the name means (#246, review of #267)
Limit:int = 3
Step(N:int)<computes>:int = N + 1
thing := class:
    (thing:)Limit:int = 10
    (thing:)Step:int = 2
Upto(A:int)<computes><decides>:int =
    A <= Limit
    A | Upto[Step(A)]
Main():void =
    for (X := Upto[1]) { Print("{X}") }
    Print("{thing{}.Limit}")
