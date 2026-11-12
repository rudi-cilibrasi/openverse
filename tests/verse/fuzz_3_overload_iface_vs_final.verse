# Regression: rb is <final> and does not implement i0, so the overloads
# are distinct. This previously failed with an overlap diagnostic.
i0 := interface:
    M():int
ra := class(i0):
    M<override>():int = 1
rb := class<final>:
    N:int = 2
Show(X:i0):string = "i0 {X.M()}"
Show(X:rb):string = "rb {X.N}"
Main():void =
    Print(Show(ra{}))
    Print(Show(rb{}))
