# expect: the parametric class box cannot have a block: clause
box(t:type) := class:
    Value:t
    block:
        Print("x")
Main():void = Print("x")
