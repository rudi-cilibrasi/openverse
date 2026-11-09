# a class without type parameters whose Verse Core type arguments it gives
# its parent class (cell(int)), below an interface that takes none (#276)
titled := interface:
    Title:string = "t"
cell(t:type) := class:
    var Value:t
intcell := class(cell(int), titled):
    X:int = 0
other := class(titled):
    Y:int = 0
Main():void =
    Ts:[]titled = array{intcell{Value := 1}, other{}}
    for (T : Ts) { Print(T.Title) }
