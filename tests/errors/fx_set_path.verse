# expect: Clear sets a var field, which its effects (<reads>) do not allow
counter := class:
    var Count:int = 0
holder := struct:
    C:counter
Clear(H:holder)<reads>:void = set H.C.Count = 0
Main():void = Clear(holder{C := counter{}})
