# expect: <private> is not allowed on a class: a class's constructor is <public>, <internal>, <protected> or <epic_internal>
counter := class<private>:
    N:int = 0
Main():void = {}
