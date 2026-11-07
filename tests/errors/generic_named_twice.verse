# expect: 3:40: ?Scale is given twice
F(X:t, ?Scale:int = 2 where t:type):t = X
Main():void = Print("{F(1, ?Scale := 2, ?Scale := 3)}")
