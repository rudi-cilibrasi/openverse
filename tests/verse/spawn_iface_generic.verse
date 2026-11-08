# spawning and racing an interface method that classes fix, in code generic
# over the interface: the generic function is compiled at each type (#204)
src(t:type) := interface:
    Next()<suspends>:t
ints := class(src(int)):
    N:int
    Next<override>()<suspends>:int =
        Sleep(0.5)
        N + 1
strs := class(src(string)):
    S:string
    Next<override>()<suspends>:string =
        Sleep(0.2)
        S
Both(A:src(t), B:src(t) where t:type)<suspends>:[]t =
    TA := spawn{A.Next()}
    TB := spawn{B.Next()}
    array{TA.Await(), TB.Await()}
First(A:src(t), B:src(t) where t:type)<suspends>:t =
    race:
        A.Next()
        B.Next()
Sp(S:src(t) where t:type)<suspends>:t =
    T := spawn{S.Next()}
    T.Await()
Main()<suspends>:void =
    Print("{Sp(ints{N := 5})} {Sp(strs{S := "z"})}")
    Is := Both(ints{N := 1}, ints{N := 2})
    for (X : Is) { Print("{X}") }
    Ss := Both(strs{S := "a"}, strs{S := "b"})
    for (X : Ss) { Print(X) }
    Print("{First(ints{N := 7}, ints{N := 8})} {First(strs{S := "p"}, strs{S := "q"})}")
