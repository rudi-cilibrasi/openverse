# Overridden methods with several values of generic classes (#283), from
# the review: a receiver typed at a subclass (Self in a subclass that has
# no override of its own, a sibling's local), and arguments whose type
# comes from the parameter (`false`, `array{}`), bound as at a generic call
box(t:type) := class:
    X:t
    Get()<transacts>:t = X | X
    Pick(W:?t)<transacts>:t = X | (if (V := W?) then V else X)
    Many(Ws:[]t)<transacts>:int = Ws.Length | 9
sbox(t:type) := class(box(t)):
    Get<override>()<transacts>:t = X
    Pick<override>(W:?t)<transacts>:t = X
    Many<override>(Ws:[]t)<transacts>:int = 7
tbox(t:type) := class(box(t)):
    Get<override>()<transacts>:t = X
nbox(t:type) := class(box(t)):
    Foo()<transacts>:[]t = for (V := Get()) { V }
Main()<transacts>:void =
    Print("a {nbox(int){X := 3}.Foo().Length}")
    S : sbox(int) = sbox(int){X := 7}
    for (V := S.Get()):
        Print("b {V}")
    Bs : []box(int) = array{box(int){X := 1}, sbox(int){X := 2}}
    for (B : Bs, V := B.Pick(false)):
        Print("c {V}")
    for (B : Bs, N := B.Many(array{})):
        Print("d {N}")
