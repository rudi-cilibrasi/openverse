# expect: interface shape cannot have a block: clause
shape := interface:
    block:
        Print("x")
Main():void = Print("x")
