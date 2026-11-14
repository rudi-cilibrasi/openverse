# expect: (super:)Foo is not in an override of Foo
# A class's block cannot call (super:) (the Book's tests, Super.versetest:
# "Calling `(super:)` from blocks is not allowed")
c := class:
    Foo():int = 42
d := class(c):
    var Bar:int = 0
    Foo<override>():int = 20
    block:
        set Bar = (super:)Foo() + 3
Main():void = Print("{d{}.Bar}")
