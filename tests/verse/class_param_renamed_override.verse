# regression test from the #39 review (p07c)
box(t:type) := class:
    Value:t
    Get():t = Value
sub(u:type) := class(box(u)):
    Get<override>():u = (super:)Get()
Main():void =
    S := sub(int){Value := 3}
    Print("{S.Get()}")
    B:box(int) = S
    Print("{B.Get()}")
