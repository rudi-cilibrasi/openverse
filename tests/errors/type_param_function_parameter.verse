# expect: no parameter of Apply determines its type parameter t
# A type parameter named only by a function type's parameter: a function
# value of type t->void takes any t below it in, so it gives none (the
# Book's tests, ParametricFunctions.versetest 348, error 3503).
Apply(G:type{_(:t):void} where t:type):void = {}
Show(X:int):void = Print("{X}")
Main():void = Apply(Show)
