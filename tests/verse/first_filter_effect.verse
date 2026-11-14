# An effect among the clauses of a first with a generator goes with a check
# that can fail, (E; true?), as a for's (the Book's tests, first.versetest:
# "same as `for`"); an iteration its later filter rejects undoes it
Find(Xs:[]int)<transacts><decides>:int = first(I->Y:Xs; (Print("y {Y}"); true?); Y > 3){I}
Main():void =
    if (V := Find[array{1, 5, 7}]) then Print("found {V}")
