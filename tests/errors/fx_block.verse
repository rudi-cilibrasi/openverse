# expect: Make constructs counter, whose block: (in counter)
counter := class:
    var Count:int = 0
    block:
        set Count = 1
Make()<computes>:counter = counter{}
Main():void = Print("{Make().Count}")
