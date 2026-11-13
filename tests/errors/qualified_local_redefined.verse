# expect: 'X' is already defined here, by a local of the enclosing code
F((local:)X:int):int =
    block:
        (local:)X:float = 5.5
    (local:)X
Main():void = {}
