# A function with several values and a defer: of its own (#283): the defer: runs as each value leaves the function (here setting a field that a for keeps)
counter := class:
    var N:int = 1
D(O:counter):int =
    defer: set O.N = 10
    O.N | 2
Main():void =
    for (R := D(counter{})) { Print("{R}") }
