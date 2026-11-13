# expect: c.F has the name of the function F (2:0), and a call could fit both, (int) and (int)
F(X:int):int = X + 1
c := class:
    F(X:int):int = X + 2
Main():void = {}
