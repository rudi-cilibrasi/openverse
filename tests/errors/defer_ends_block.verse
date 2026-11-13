# expect: defer: is a statement: it has no value, so it cannot end a block
# (Book of Verse ch. 7; a void function's body too)
Log(Msg:string):void = Print(Msg)
Run():void =
    Log("A")
    defer:
        Log("B")
Main():void = Run()
