# overriding a method with type parameters of its own, and calls of it
# dispatched on the receiver's class: its type parameters (named as the
# override likes) are inferred from the arguments, as for a generic call

shape := class<abstract>:
    Tag(X:u where u:type):tuple(string, u)
square := class(shape):
    Tag<override>(Y:w where w:type):tuple(string, w) = ("square", Y)
circle := class(shape):
    Tag<override>(X:u where u:type):tuple(string, u) = ("circle", X)
box(t:type) := class:
    Value:t
    Pair(Other:u where u:type):tuple(t, u) = (Value, Other)
sub(t:type) := class(box(t)):
    Pair<override>(Other:u where u:type):tuple(t, u) = (Value, Other)
Use(B:box(w), X:w where w:type):tuple(w, int) = B.Pair(3)
Use2(B:box(u), X:u where u:type):tuple(u, int) = B.Pair(3)
Main():void =
    Ss:[]shape = array{square{}, circle{}}
    for (S : Ss):
        T := S.Tag(7)
        Print("{T(0)} {T(1)}")
        U := S.Tag("s")
        Print("{U(0)} {U(1)}")
    Bs:[]box(int) = array{box(int){Value := 1}, sub(int){Value := 2}}
    for (B : Bs):
        P := B.Pair("x")
        Print("{P(0)} {P(1)}")
    Q := Use(sub(string){Value := "v"}, "w")
    Print("{Q(0)} {Q(1)}")
    R := Use2(sub(logic){Value := true}, false)
    Print("{R(1)}")
