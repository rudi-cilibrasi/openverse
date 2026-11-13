# expect: (local:)X: (local:) qualifies a function's locals, and X is a member of the module M
M := module:
    (local:)X:int = 5
Main():void = {}
