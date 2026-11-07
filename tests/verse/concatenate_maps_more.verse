# ConcatenateMaps (#89 review): values of subclasses joined, arguments
# evaluated left to right, a <decides> argument in a failure context, a
# leading map{} typed by a later map, and a discarded result
shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R

Noisy(N:int, M:[int]int):[int]int =
    Print("arg {N}")
    M

Pick(B:logic)<decides>:[int]int =
    B?
    map{9 => 9}

Main():void =
    Shapes := ConcatenateMaps(map{1 => square{S := 2}}, map{2 => circle{R := 1}})
    for (K -> V : Shapes) { Print("{K}: {V.Area()}") }
    M := ConcatenateMaps(Noisy(1, map{1 => 10}), Noisy(2, map{2 => 20}), Noisy(3, map{1 => 30}))
    for (K -> V : M) { Print("{K}={V}") }
    if (P := ConcatenateMaps(map{1 => 1}, Pick[true])) then Print("{P.Length}")
    if (P := ConcatenateMaps(map{1 => 1}, Pick[false])) then Print("{P.Length}") else Print("failed")
    X := ConcatenateMaps(map{}, map{1 => "a"})
    Print("{X.Length}")
    ConcatenateMaps(M, map{5 => 5})
