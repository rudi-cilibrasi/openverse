# expect: 5:18: no parameter of Empty determines its type parameter t
# A type parameter only the result names: no call can give it (the Book's
# rule, ParametricFunctions.versetest 336, error 3503), refused where it is
# declared (before, at the call that could not infer it).
Empty(N:int where t:type):[]t = array{}

Main():void = Print("{Empty(3).Length}")
