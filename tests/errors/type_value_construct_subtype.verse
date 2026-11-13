# expect: T{…} constructs through a value of concrete_subtype(…), and T is a subtype(c)
c := class{}
F(T:subtype(c)):c = T{}
Main():void = {}
