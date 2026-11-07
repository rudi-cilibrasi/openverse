# expect: so it cannot implement the interface
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
