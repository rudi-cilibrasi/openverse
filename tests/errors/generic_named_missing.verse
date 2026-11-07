# expect: 3:23: F needs the argument ?Scale, which has no default
F(X:t, ?Scale:int where t:type):t = X
Main():void = Print("{F(1)}")
