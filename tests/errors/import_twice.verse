# expect: Twice is defined twice
using{"lib/twice"}
Twice(X:int):int = X + X
Main():void = Print("x")
