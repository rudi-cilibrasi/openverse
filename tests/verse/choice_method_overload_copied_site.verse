# A method with two lists, one with several values and one with one, called
# in clauses after a composed choice, which are compiled once for each of its
# alternatives, and before another composed choice with a call of a lazily
# taken function that also calls itself in a failure context of its code
# (#723): the call's overload was found only in the copies, so the place
# itself was taken to be of no overload, and the function the clauses later
# move into called the family's stub: "c.Mv has several values, but a call of
# it in $cont… is compiled as one of a method of one value". The copies'
# overload is the place's.
Walk(N:int, A:int)<transacts><decides>:int =
    N >= 0
    not (Walk[N - 1, A] >= 3)
    (2 | A | Walk[N - 1, A])
c := class:
    var Na:int = 0
    var Nb:int = 0
    Mv(P:int)<transacts>:int = P * 5 | P + 7
    Mv(P:int, Q:int)<transacts>:int = P * 10 + Q
    Run()<transacts>:void =
        O := option{X := (Nb | ((-1 | Na) + 2)); Y := Mv(Na); Z := (2 | Walk[1, Nb]); Y > Z}
        if (V := O?) then Print("o {V}") else Print("o none")
Main():void =
    c{}.Run()
