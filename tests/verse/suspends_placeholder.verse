# suspends methods of an interface whose classes all fix its type argument, on receivers from fields and for loops (#157)
src(t:type) := interface:
    Next()<suspends>:t
ints := class(src(int)):
    N:int
    Next<override>()<suspends>:int =
        Sleep(0.5)
        N + 1
holder(t:type) := class:
    S:src(t)
G(H:holder(t) where t:type)<suspends>:t = H.S.Next()
G2(Hs:[]src(t), X:t where t:type)<suspends>:t =
    var R:t = X
    for (S : Hs):
        set R = S.Next()
    R
Main()<suspends>:void =
    Print("{G(holder(int){S := ints{N := 1}})}")
    Print("{G2(array{ints{N := 5}, ints{N := 6}}, 0)}")
