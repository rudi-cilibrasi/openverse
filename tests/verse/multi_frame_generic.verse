# (#283) A generic one: its frames keep values of its type parameter.
Rep(X:t, N:int where t:type)<transacts><decides>:[]t =
    N >= 0
    E:[]t = array{}
    R := Rep[X, N - 1] | E
    Print("rep {N}")
    R + array{X}
Loud(X:t, N:int where t:type)<transacts><decides>:[]t =
    Print("enter {N}")
    N >= 0
    E:[]t = array{}
    R := Loud[X, N - 1] | E
    R + array{X}
Main()<transacts>:void =
    for (V := Rep["a", 2]) { Print("v {V.Length}") }
    if (V := Rep[7, 3], V.Length = 2) then Print("first {V.Length}")
    if (V := Loud[7, 3], V.Length = 2) then Print("first {V.Length}")
