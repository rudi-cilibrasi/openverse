# expect: which must be comparable
cell(t:type) := class:
    var Value:t
base(t:subtype(comparable)) := class:
    X:t
    Same(Y:t):logic = logic{X = Y}
sub(t:type) := class(base(t)):
    Z:int = 0
Main():void =
    C := cell(int){Value := 1}
    S := sub(cell(int)){X := C}
    B:base(cell(int)) = S
    if (B.Same(C)?) then Print("same") else Print("differ")
    if (B.Same(cell(int){Value := 1})?) then Print("same") else Print("differ")
