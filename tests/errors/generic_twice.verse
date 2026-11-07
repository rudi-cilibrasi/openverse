# expect: type parameter t is declared twice
F(X:t where t:type, t:subtype(comparable)):t = X

Main():void = Print("x")
