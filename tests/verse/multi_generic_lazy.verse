# a generic generator taken lazily, in a for and an if, at two types (#235, #246)
Elements(A:[]t, I:int where t:type)<decides>:t =
    I < A.Length
    A[I] | Elements[A, I + 1]
Main():void =
    for (X := Elements[array{10, 20, 30}, 0]) { Print("{X}") }
    if (S := Elements[array{"x", "yy", "zzz"}, 0], S.Length > 1) then Print(S)
