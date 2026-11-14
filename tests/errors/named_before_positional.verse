# expect: a positional argument after a named one: the named arguments come last
Subtract(A:int, ?B:int = 0):int = A - B
Main():void = Print("{Subtract(?B := 1, 42)}")
