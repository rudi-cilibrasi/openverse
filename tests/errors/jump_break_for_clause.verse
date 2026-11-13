# expect: 6:31: break cannot leave a failure context
# A break in a for's clauses (SOL-4199-BreakFromIf.versetest:15)
Main():void =
    var N:int = 0
    loop:
        for (I := 1..2, I > 1, break) { set N += I }
        break
