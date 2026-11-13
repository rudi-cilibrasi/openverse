# expect: <protected> is not allowed on a struct: its constructor is <public>, <internal> or <epic_internal>
point := struct<protected>:
    X:int = 0
Main():void = {}
