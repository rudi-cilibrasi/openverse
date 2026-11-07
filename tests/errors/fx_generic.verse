# expect: Touch sets a var field, which its effects (<reads>) do not allow
counter := class:
    var Count:int = 0
Touch(X:t, C:counter where t:type)<reads>:t =
    set C.Count = 1
    X
Main():void = Print("{Touch(1, counter{})}")
