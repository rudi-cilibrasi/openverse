# expect: Peek reads a var field, which its effects (<computes>) do not allow
counter := class:
    var Count:int = 0
Peek(C:counter)<computes>:int = C.Count
Main():void = Print("{Peek(counter{})}")
