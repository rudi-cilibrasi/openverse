# a tuple expands into a function's parameters; several arguments make its one array parameter (#134)
Describe(Count:int, Name:string):string = "{Count} {Name}"
Sum(Xs:[]int):int =
    var T:int = 0
    for (X : Xs) { set T += X }
    T
Pair():tuple(int, string) = (3, "three")
Main():void =
    MyTuple := (1, "two")
    Print(Describe(MyTuple))
    Print(Describe(Pair()))
    Print(Describe((2, "x")))
    Triple := (10, 20, 30)
    Print("{Sum(Triple)} {Sum(1, 2, 3, 4)} {Sum(array{5})}")
