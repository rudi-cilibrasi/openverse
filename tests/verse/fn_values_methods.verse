# methods as values (#210): a value holds its receiver (a counter's state
# changes through it), a method named alone in a method is Self's, an
# interface's method dispatches to each class's, a generic class's method
# is passed to generic code
counter := class:
    var N:int = 0
    Add(X:int):int =
        set N += X
        N
    Adder():int->int = Add
shape := interface:
    Area():int
sq := class(shape):
    S:int
    Area<override>():int = S * S
rect := class(shape):
    W:int
    H:int
    Area<override>():int = W * H
box(t:type) := class:
    V:t
    Get():t = V
    Put(X:t):void = Print("put")
Apply(F:int->int, X:int):int = F(X)
Run(F:type{_():int}):int = F()
Fetch(F:type{_():t} where t:type):t = F()
Main():void =
    C := counter{}
    Print("{Apply(C.Add, 2)} {Apply(C.Add, 3)} {C.N}")
    G := C.Adder()
    Print("{G(10)} {C.N}")
    Shapes:[]shape = array{sq{S := 3}, rect{W := 2, H := 5}}
    for (S : Shapes) { Print("{Run(S.Area)}") }
    B := box(string){V := "b"}
    Print(Fetch(B.Get))
    P := B.Put
    P("x")
