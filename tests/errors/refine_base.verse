# expect: 2:0: a refinement type refines an int or a float, not string
b := type{_X:string where _X < 1}
Main():void = Print("x")
