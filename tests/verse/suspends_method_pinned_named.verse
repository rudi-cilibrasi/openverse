# the same through a <suspends> method (#175)
box(t:type) := class:
    V:t
    Get(X:t, ?Opt:?int = false)<suspends>:t = V
int_box := class(box(int)):
    Get<override>(X:int, ?Opt:?int = false)<suspends>:int =
        Sleep(0.1)
        X + (Opt? or 0)
G(B:box(t), X:t where t:type)<suspends>:t =
    B.Get(X)
Main()<suspends>:void =
    Print("{G(int_box{V := 1}, 10)}")
