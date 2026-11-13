# expect: 5:19: break cannot leave a failure context
# A break in an if's condition (SOL-4199-BreakFromIf.versetest:4, 3658)
Main():void =
    loop:
        if (true?, break) then Print("x")
        break
