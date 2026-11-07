# expect: field 'N' of c must have the type it inherits, int, not string
i := interface:
    N:int = 0
j := interface:
    N:string = "x"
c := class(i, j):
    M:int = 0
Main():void = Print("x")
