# expect: Clear sets a var field, which its effects (<reads>) do not allow
counter := class:
    var Count:int = 0
Clear(C:counter)<reads>:void = set C.Count = 0
Main():void = Clear(counter{})
