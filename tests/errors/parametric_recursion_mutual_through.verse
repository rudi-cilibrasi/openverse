# expect: the fields of a name b, and those of b name a through others: parametric types cannot be mutually recursive
# a cycle through a third parametric class, in a map's value and a tuple
a(t:type) := class:
    B:?b(t) = false
b(t:type) := class:
    C:[int]c(t) = map{}
c(t:type) := class:
    A:tuple(int, ?a(t)) = (0, false)
Main():void = Print("ok")
