# expect: (super:)Method is not in an override of Method
# An override of Method2 cannot call (super:)Method (the Book's tests,
# Super.versetest: "super on another method")
super_class := class:
    Method():int = 41
    Method2():int = 14
child_class := class(super_class):
    Method<override>():int = 42
    Method2<override>():int = (super:)Method()
Main():void = Print("{child_class{}.Method2()}")
