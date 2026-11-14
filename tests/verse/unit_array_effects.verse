counter := class:
    var Ticks:int = 0

Empty(C:counter, Tag:string):void =
    set C.Ticks += 1
    Print("{Tag} {C.Ticks}")

Pair(A:[]int, B:[]int)<computes>:int = A.Length + B.Length

Main():void =
    C := counter{}
    Print("pair {Pair(Empty(C, "left"), Empty(C, "right"))}")
    V:void = Empty(C, "bind")
    A:[]string = V
    Print("array {A.Length}")
    U:true = false
    FromTrue:[]int = U
    FromLiteral:[]int = ()
    Print("units {FromTrue.Length} {FromLiteral.Length}")
    Voids:[]void = array{8, 9}
    Arrays:[][]int = Voids
    if (First := Arrays[0], Second := Arrays[1]):
        Print("nested {Arrays.Length} {First.Length} {Second.Length}")
    T:tuple(void, int) = (Empty(C, "tuple"), 7)
    Converted:tuple([]float, int) = T
    Print("tuple {Converted(0).Length} {Converted(1)}")
    O:?void = option{Empty(C, "option")}
    P:?[]int = O
    if (Value := P?) then Print("option {Value.Length}")
    M:[int]void = map{2 => Empty(C, "map")}
    N:[int][]char = M
    if (Text := N[2]) then Print("map {Text.Length}")
    S:string = Empty(C, "string")
    Print("string {S.Length}")
    if (Discard:[]int = Empty(C, "rolled back"), false?):
        Print("wrong {Discard.Length}")
    Print("kept {C.Ticks}")
