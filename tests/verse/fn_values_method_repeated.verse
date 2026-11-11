# A repeated class parameter is related by function-shape pins.
box(t:type) := class:
    V:t
    Same(X:t):t = X
Main():void =
    B := box(int){V := 1}
    F := B.Same
    Print("{F(2)}")
