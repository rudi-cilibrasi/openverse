# expect: is named nowhere in its signature, so nothing can give it one
# A type parameter named nowhere in its function's signature is refused where it is
# declared (Book of Verse tests, ParametricFunctions.versetest:374, 3503).
Forget(X:a where a:type,b:type):a=X
Use(X:t where t:type):void=
    F:type{_(:t):t}=Forget
Main():void=Use(3)
