# expect: is named nowhere in its signature, so nothing can give it one
# A type parameter named nowhere in its function's signature is refused where it is
# declared (Book of Verse tests, ParametricFunctions.versetest:374, 3503).
box:=class:
    Empty(X:int,Y:int where u:type):int=X+Y
Main():void=
    F:type{_(:tuple(int,int)):int}=box{}.Empty
