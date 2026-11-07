# expect: the constant Shared would hold an object with var fields or of a <unique> class
counter := class:
    var Count:int = 0
Shared:counter = counter{}
Main():void = Print("{Shared.Count}")
