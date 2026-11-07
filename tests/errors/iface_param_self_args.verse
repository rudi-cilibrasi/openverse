# expect: the Verse Core type of class loopy would contain itself
holder(t:type) := interface:
    var Item:t
loopy := class(holder(?loopy)):
    K:int = 0
Main():void = Print("x")
