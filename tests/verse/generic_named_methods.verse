# named parameters on generic methods (#119): a default sees the receiver's fields
c := class:
    Base:int = 10
    Tag(X:t, ?Extra:int = Base where t:type):tuple(t, int) = (X, Extra)
box(t:type) := class:
    V:t
    With(?Other:t = V):t = Other
Main():void =
    C := c{}
    P := C.Tag("a")
    Q := C.Tag(1, ?Extra := 5)
    Print("{P(0)} {P(1)} {Q(1)}")
    B := box(string){V := "v"}
    Print(B.With())
    Print(B.With(?Other := "w"))
