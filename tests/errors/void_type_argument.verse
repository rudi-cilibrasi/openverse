# expect: expected tuple(), found int (in a call of class1.Foo)
# (Book of Verse ch. 2: a type parameter bound to void takes the empty value
# alone, the type true; Void.versetest:246)
class1(t:type) := class:
    Foo(:t):void = {}
Main():void =
    X:int = 1
    class1(void){}.Foo(X)
