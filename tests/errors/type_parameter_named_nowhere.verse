# expect: 4:12: the type parameter t of F is named nowhere in its signature
# A type parameter that no parameter's type and not the result's names can
# be given by nothing (Book of Verse tests, ParametricFunctions.versetest:374, 3503).
F(X:u where t:type, u:type):u = X
Main():void = Print("{F(1)}")
