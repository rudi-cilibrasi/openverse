# expect: 6:12: break cannot leave a failure context
# A break in logic{} (SOL-4199-BreakFromIf.versetest:60)
Main():void =
    loop:
        X := logic:
            break
        break
