# expect: 4:56: this filter of first is a literal or a name, which cannot fail
# A filter of first must be able to fail, as a for's (Book of Verse tests,
# FlowControl/first.versetest:28-31, 3513).
F(X:int, Xs:[]int)<decides>:int = first(I->Y:Xs; X = Y; I){I}
Main():void = {}
