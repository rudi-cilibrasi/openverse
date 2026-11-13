# expect: 4:28: an extension method is a function, (R:t).M(…)<effects>:type = body (Book of Verse ch. 6)
# An extension method is a function, not a constructor
c := class{X:int = 0}
(I:int).Make<constructor>() := c:
    X := I
Main():void = {}
