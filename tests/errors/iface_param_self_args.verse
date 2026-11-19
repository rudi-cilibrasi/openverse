# expect: the Verse Core type of class loopy would contain itself
# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
holder(t:type) := interface:
    var Item:t
loopy := class(holder(?loopy)):
    K:int = 0
Main():void = Print("x")
