# regression test from the #65 review (cap4)
box(t:type) := class:
    Value:t
    Pair(Other:w where w:type):tuple(t, w) = (Value, Other)
sub(t:type) := class(box(t)):
    Pair<override>(Other:u where u:type):tuple(t, u) = (Value, Other)
subsub(u:type) := class(sub(u)):
    X:int = 0
Main():void =
    Bs:[]box(int) = array{box(int){Value := 1}, sub(int){Value := 2}, subsub(int){Value := 3}}
    for (B : Bs):
        P := B.Pair("x")
        Print("{P(0)} {P(1)}")
