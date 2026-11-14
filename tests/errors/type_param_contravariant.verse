# expect: no parameter of Use determines its type parameter t
# A class that only takes its type parameter in (a method's parameter) is
# contravariant in it: an argument of type sink(t) gives no t, as any
# sink(u) below it is one (the Book's tests, ParametricFunctions.versetest
# 356-372, error 3503).
sink(t:type) := class:
    Take(X:t):void = {}
Use(S:sink(t) where t:type):void = {}
Main():void = Use(sink(int){})
