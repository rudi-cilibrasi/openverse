# expect: 5:21: break cannot leave a failure context
# A break in the left of or (SOL-4199-BreakFromIf.versetest:74)
Main():void =
    loop:
        X := (true?; break) or 1
        break
