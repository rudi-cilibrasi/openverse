# expect: c inherits a default for field 'N' from both i and j
i := interface:
    N:int = 0
j := interface:
    N:int = 1
c := class(i, j):
    M:int = 0
Main():void = Print("x")
