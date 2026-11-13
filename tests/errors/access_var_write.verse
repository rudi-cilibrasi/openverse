# expect: Count of tally cannot be set here: its var is <private>: only tally's own code may use it
# (Book of Verse ch. 12, "Separating Read and Write Access"; VarAccessSpecifiers.versetest:37: error 3509)
tally := class:
    var<private> Count<public>:int = 0
    Bump<public>():void = set Count += 1
Main():void =
    T := tally{}
    T.Bump()
    set T.Count = 5
