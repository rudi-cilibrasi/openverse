# expect: (M:)X: X is defined in the module M.N, not in M: a definition's qualifier names where it is defined
M := module:
    N := module:
        (M:)X:int = 1
Main():void = {}
