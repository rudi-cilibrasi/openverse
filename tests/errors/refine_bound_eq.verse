# expect: 2:0: a refinement's condition is <, <=, > or >=, not =
b := type{_X:int where _X = 3}
Main():void = Print("x")
