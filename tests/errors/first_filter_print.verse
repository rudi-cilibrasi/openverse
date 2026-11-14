# expect: this filter cannot fail
# A print among the clauses of a first with a generator is a filter that
# cannot fail, as a for's (the Book's tests, first.versetest: "same as `for`")
Find(Xs:[]int)<transacts><decides>:int = first(I->Y:Xs; Print("y {Y}"); Y > 3){I}
Main():void = {}
