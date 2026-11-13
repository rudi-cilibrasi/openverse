# expect: 6:19: no overload of Double takes (string)
# No overload of the extension method takes the receiver's type
(N:int).Double():int = N * 2
(F:float).Double():float = F * 2.0
Main():void =
    X := "a".Double()
