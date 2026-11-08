# expect: 'Same' is a method of box that cannot be used as a value
# its type repeats the class's type parameter (that would need #171)
box(t:type) := class:
    V:t
    Same(X:t):t = X
Main():void =
    B := box(int){V := 1}
    F := B.Same
    Print("{F(2)}")
