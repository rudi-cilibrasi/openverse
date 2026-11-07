# Wrongly rejected as overlapping overloads: rb is <final> and does not implement i0,
# so no value is both. LANGUAGE.md: a class or interface overlaps an interface or a class
# above or below it; i0 and rb are neither.
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
