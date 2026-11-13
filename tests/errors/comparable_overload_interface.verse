# expect: Comp is defined twice with parameters a call cannot tell apart, (comparable, comparable) and (Interface, Interface)
# a <unique> interface is comparable: these are ambiguous (Book of Verse
# Tests/ComparableInterface.versetest 140 to 146)
Interface := interface<unique> {
    Method1():void
}
Comp(X:comparable, Y:comparable):void = 42
Comp(X:Interface, Y:Interface):void = 42
