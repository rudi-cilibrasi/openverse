# expect: cannot cast an expr(t) to pairE here: the cast opens pairE's type argument a for the code after it, outside which its value, an expr(a'), would name what is unknown (#250)
# (#243, #250) a for's clause after a cast that opens type arguments binds
# a name the body uses, of an opened type, which the body, cast again,
# would have no name for
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
Tags(Es:[]expr(t) where t:type):[]string =
    for (E : Es, Print("e"), P := pairE[E], L := P.L) { L.Tag() }
Main():void = Print("{Tags(array{lit{V := 1}}).Length}")
