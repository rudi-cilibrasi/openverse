# expect: is named nowhere in its signature, so nothing can give it one
# A type parameter named nowhere in its function's signature is refused where it is
# declared (Book of Verse tests, ParametricFunctions.versetest:374, 3503).
box:=class:
    Empty(X:int where t:type)<computes>:int=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Main():void=Print("{Apply(box{}.Empty,7)}")
