# expect: 'Shadow' is ambiguous here: the local (local:)Shadow and a definition outside this code are both named so
M := module:
    Shadow<public>:int = 10
    F():int =
        (local:)Shadow:int = 1
        Shadow
Main():void = {}
