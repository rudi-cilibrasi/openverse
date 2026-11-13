# expect: 'X' is already defined here, as (local:)X
F((local:)X:int):int =
    block:
        X:int = 5
    (local:)X
Main():void = {}
