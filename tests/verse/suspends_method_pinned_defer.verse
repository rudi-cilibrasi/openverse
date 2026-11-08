# refined calls under defer: in the caller, in a race arm, and when the
# task running one is cancelled (#171)
box(t:type) := class:
    V:t
    Get(D:float)<suspends>:t = V
int_box := class(box(int)):
    Get<override>(D:float)<suspends>:int =
        defer:
            Print("get {D} exits")
        Sleep(D)
        V + 1
G(B:box(t), D:float where t:type)<suspends>:t =
    defer:
        Print("G {D} exits")
    B.Get(D)
H(B:box(t) where t:type)<suspends>:t =
    race:
        G(B, 2.0)
        block:
            defer:
                Print("arm exits")
            B.Get(1.0)
Work()<suspends>:int =
    G(int_box{V := 5}, 3.0)
Main()<suspends>:void =
    Print("{H(int_box{V := 1})}")
    T := spawn{Work()}
    Sleep(1.0)
    T.Cancel()
    Print("cancelled")
