# expect: in a function type, every parameter after a named one must be named
# (Book of Verse ch. 6, #503)
Main():void =
    F:type{_(?A:int, :int):int} = F
    Print("bad")
