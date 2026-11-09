# expect: 4:0: D has several values and a defer:
counter := class:
    var N:int = 1
D(O:counter):int =
    defer: set O.N = 10
    O.N | 2
Main():void =
    for (R := D(counter{})) { Print("{R}") }
