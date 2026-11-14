# expect: the fields of t1 name t2, and those of t2 name t1: parametric types cannot be mutually recursive (Book of Verse ch. 10, "Disallowed: Mutual Recursion")
t1(t:type) := class:
    Next:?t2(t)
t2(t:type) := class:
    Next:?t1(t)
Main():void = Print("ok")
