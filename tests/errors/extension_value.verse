# expect: 5:10: Double is an extension method, which must be called, X.Double(…): it is no value (Book of Verse ch. 6)
# An extension method must be called (Book of Verse ch. 6): it is no value
(N:int).Double():int = N * 2
Main():void =
    F := 5.Double
