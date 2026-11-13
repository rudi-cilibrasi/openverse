# expect: 9:28: this call of DoSomething is ambiguous: it fits DoSomething as written, and the extension method DoSomething with Self as its receiver (Book of Verse ch. 6)
# A bare call in a method that fits both a function and an extension method
# with Self (Book of Verse tests, error 3518)
my_class := class:
    X:int
(M:my_class).DoSomething():int = 40 + M.X
DoSomething():int = 21
my_subclass := class(my_class):
    Some():int = DoSomething()
Main():void = {}
