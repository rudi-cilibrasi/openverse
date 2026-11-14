# expect: (super:)Foo is not in an override of Foo
# A field's default is no override: it cannot call (super:)
c := class:
    Foo():int = 42
d := class(c):
    Foo<override>():int = 20
    Bar:int = (super:)Foo() + 3
Main():void = Print("{d{}.Bar}")
