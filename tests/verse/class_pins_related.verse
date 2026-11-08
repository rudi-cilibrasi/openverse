# classes that fix a type argument to a type over another one (#209)
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
optpair(t:type) := class(pair(?t, t)):
    Get<override>():?t = option{B}
nestpair(t:type) := class(pair([]t, t)):
    Get<override>():[]t = array{B, B}
Show(P:pair(?int, int)):string = if (V := P.Get()?) then "{V}" else "none"
Main():void =
    Print(Show(pair(?int, int){A := false, B := 5}))
    Print(Show(optpair(int){A := false, B := 7}))
    N:pair([]int, int) = nestpair(int){A := array{}, B := 3}
    Print("{N.Get().Length}")
