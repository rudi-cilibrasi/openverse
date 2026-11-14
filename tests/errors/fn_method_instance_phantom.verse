# expect: is named nowhere in its signature, so nothing can give it one
# A type parameter named nowhere in its function's signature is refused where it is
# declared (Book of Verse tests, ParametricFunctions.versetest:374, 3503).
box:=class:
    Same(X:t where t:type,u:type):t=X
Main():void=
    F:type{_(:int):int}=box{}.Same
    Print("wrong")
