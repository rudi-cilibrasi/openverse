# expect: 3:27: F has no parameter ?Size
F(X:t, ?Scale:int = 2 where t:type):t = X
Main():void = Print("{F(1, ?Size := 2)}")
