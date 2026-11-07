# expect: struct s contains itself
cell(t:type) := class:
    A:t
s := struct:
    X:?c
c := class(cell(s)):
    M:int = 0
Main():void = Print("x")
