# expect: a top-level definition must start at column 0
# This is a rejection case, not a runtime closure/state oracle.
Make():type{_():int} =
    var Count:int = 0
    Next():int =
        set Count += 1
        Count
    Next
Main():void = Print(Make()())
