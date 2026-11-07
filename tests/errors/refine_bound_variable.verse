# expect: 2:0: a refinement's bound is a literal number, not a variable or an expression
b := type{_X:int where _X <= Y}
Main():void = Print("x")
