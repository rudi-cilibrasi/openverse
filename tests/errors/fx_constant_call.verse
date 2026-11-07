# expect: Peek calls Shared, which has the effect <reads>
counter := class:
    var Count:int = 0
Fresh()<reads>:int = 7
Shared:int = Fresh()
Peek()<computes>:int = Shared
Main():void = Print("{Peek()}")
