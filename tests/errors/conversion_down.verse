# expect: c1(…) converts to a supertype, and c0 is not below c1
c0 := class{}
c1 := class(c0){}
F():void = c1(c0{})
Main():void = {}
