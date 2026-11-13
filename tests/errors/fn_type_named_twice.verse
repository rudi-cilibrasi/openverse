# expect: a function type names its parameter ?A twice
# (#503)
Twice(?A:int):int = A
Main():void =
    F:type{_(?A:int, ?A:int):int} = Twice
    Print("bad")
