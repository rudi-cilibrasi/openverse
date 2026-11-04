# The failable array methods (Book of Verse §9.1).
Show(A:[]int):string =
    var S:string = ""
    for (I -> X : A):
        if (I > 0) { set S += " " }
        set S += "{X}"
    "[{S}]"

Main():void =
    A := array{10, 20, 30, 40, 50}
    if (B := A.Slice[1, 3]) { Print("Slice[1, 3] = {Show(B)}") }
    if (B := A.Slice[3]) { Print("Slice[3] = {Show(B)}") }
    if (not A.Slice[4, 2]) { Print("Slice[4, 2] fails") }
    if (I := A.Find[30]) { Print("Find[30] = {I}") }
    if (not A.Find[31]) { Print("Find[31] fails") }
    if (B := A.RemoveElement[0]) { Print("RemoveElement[0] = {Show(B)}") }
    if (not A.RemoveElement[5]) { Print("RemoveElement[5] fails") }
    if (B := A.ReplaceElement[4, 7]) { Print("ReplaceElement[4, 7] = {Show(B)}") }
    if (B := A.Insert[2, array{1, 2}]) { Print("Insert[2, array\{1, 2\}] = {Show(B)}") }
    if (B := A.Insert[5, array{9}]) { Print("Insert[5, array\{9\}] = {Show(B)}") }
    if (not A.Insert[6, array{9}]) { Print("Insert[6, …] fails") }
    if (S := "Hello, Verse".Slice[7]) { Print(S) }
