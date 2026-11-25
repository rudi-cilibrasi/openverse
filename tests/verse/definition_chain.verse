# A definition whose value is a definition (#724): "the result of a
# definition is its value" (the Book's tests, Definitions.versetest:37,
# `X:int = Y:int = 4; X=4; Y=4`), and both names are defined in the scope
# the definition is in, the inner one first (Epic's compiler and Verse VM,
# UEFN 43.12, followup-refused/definition-in-expression: x 4 y 4). A var's
# result is its contents.
Count(Xs:[]int):int =
    N:int = M := Xs.Length
    N + M
Main():void =
    X:int = Y:int = 4
    Print("x {X} y {Y}")
    A := B := C:int = 7
    Print("{A} {B} {C}")
    var V:int = W:int = 2
    set V += W
    Print("{V} {W}")
    # the inner one a var: the outer has its contents
    P:int = var Q:int = 3
    set Q += 1
    Print("{P} {Q}")
    # in an if's conditions, and its branch
    if (E:int = F:int = 5, E = F) then Print("e {E} f {F}")
    # in a block, whose scope they are
    G := block:
        H:int = I:int = 6
        H + I
    Print("{G} {Count(array{1, 2, 3})}")
    # the value is elaborated once
    var Calls:int = 0
    J:int = K:int = block:
        set Calls += 1
        Calls * 10
    Print("{J} {K} {Calls}")
