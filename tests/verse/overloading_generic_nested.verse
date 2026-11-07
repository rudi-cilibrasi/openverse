# generic and non-generic overloads of one arity, nested 20 deep (#95 review):
# resolved by matching the arguments' types against the patterns
F(X:?t where t:type):int = 0
F(X:int):int = X + 1
Main():void = Print("{F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(1))))))))))))))))))))}")
