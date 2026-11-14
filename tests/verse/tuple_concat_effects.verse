counter := class { var N:int = 0 }
holder := class { var Values:[]int = array{9} }

Pair(C:counter, Tag:string, N:int):tuple(int, int) =
    set C.N += 1
    Print("{Tag} {C.N}")
    (N, N + 1)

Replace(H:holder, C:counter):tuple(int, int) =
    set H.Values = array{7}
    Pair(C, "replace", 8)

Main():void =
    C := counter{}
    A := Pair(C, "left", 1) + Pair(C, "right", 3)
    if (A = array{1, 2, 3, 4}) then Print("ordered {C.N}")
    H := holder{}
    set H.Values += Replace(H, C)
    if (H.Values = array{7, 8, 9}) then Print("updated {C.N}")
    if (Discard := Pair(C, "rolled back", 5) + (7, 8), false?):
        Print("wrong {Discard.Length}")
    Print("kept {C.N}")
