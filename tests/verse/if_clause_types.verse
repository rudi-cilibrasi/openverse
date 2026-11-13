# An if whose condition has a clause D := F[X], or F[X], takes the type any
# if takes with no expected type (ifBranches, #32, #366, #583), whatever F is
# (an array, a <decides> function, a class) and wherever the clause is: an
# else that has no type alone (array{}, map{}, false) has the then's. Only a
# cast that refines type arguments (#243) is typed under its refinement, and
# its branch is at the expected type as with the cast alone.
box(t:type) := class:
    V:t
ibox := class(box(int)):
    W:int = 2
animal := class:
    N:int = 1
dog := class(animal):
    D:int = 3
Pos(K:int)<decides>:int =
    K > 0
    K
F(B:box(t), A:animal, Xs:[]int, K:int where t:type):void =
    I := if (X := Xs[1], K > -5) then array{X} else array{}
    C := if (X := Pos[K], K > -5) then map{X => 1} else map{}
    D := if (X := dog[A], K > -5) then array{X.D} else array{}
    E := if (Xs[1], K > -5) then array{K} else array{}
    R := if (X := ibox[B]) then array{X.W} else array{}
    M := if (X := ibox[B]) then map{X.W => 1} else map{}
    O := if (X := ibox[B]) then option{X.W} else false
    T:?int = if (X := ibox[B], K > -5) then false else option{7}
    U:?int = if (K > -5, X := ibox[B]) then false else option{7}
    Print("{I.Length} {C.Length} {D.Length} {E.Length} {R.Length} {M.Length} {O? or 0} {T? or 0} {U? or 0}")
Main():void =
    F(ibox{V := 1}, dog{}, array{4, 5}, 1)
    F(box(string){V := "a"}, animal{}, array{}, -1)
