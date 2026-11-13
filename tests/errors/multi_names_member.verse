# expect: 8:18: Small has several values and uses Limit, which is also the name of a member of Self here
# (#283) inlined in a method of a class with a field named like a name its body uses: there it would mean the field
Limit:int = 3
Small():int = 1 | Limit
thing := class:
    (thing:)Limit:int = 10
    Show():void =
        for (X := Small()) { Print("{X}") }
Main():void = thing{}.Show()
