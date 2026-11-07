# expect: 2:0: a float refinement's bound is a float literal (write 142.0)
b := type{_X:float where _X <= 142}
Main():void = Print("x")
