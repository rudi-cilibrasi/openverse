# expect: the Verse Core type of class loopy would contain itself
cell(t:type) := class:
    var Item:t
loopy := class(cell(?loopy)):
    K:int = 0
Main():void = Print("x")
