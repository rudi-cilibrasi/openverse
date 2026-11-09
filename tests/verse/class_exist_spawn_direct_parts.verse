# a spawn of an inherited method that reads type arguments from its receiver,
# in a class that gives them as composites of its own (#209): the task's root
# is generic at the spawner's type parameters, and its slots of their types
# start as parts of the receiver's fields, through tuples and objects
# (mid(tuple(u, v), int)'s a, holder(u)'s H; the first shape is from the
# review of #321)
job(t:type) := class<abstract>:
    Run()<suspends>:t
holder(u:type) := class:
    H:u
mid(a:type, b:type) := class(job(tuple(a, b))):
    A:a
    B:b
    Run<override>()<suspends>:tuple(a, b) =
        Sleep(0.1)
        (A, B)
child(u:type, v:type) := class(mid(tuple(u, v), int)):
    Kick():task(tuple(tuple(u, v), int)) = spawn{(super:)Run()}
child3(u:type) := class(mid(holder(u), int)):
    Kick():task(tuple(holder(u), int)) = spawn{(super:)Run()}
child4(u:type, v:type) := class(mid(tuple(tuple(u, int), v), u)):
    Kick():task(tuple(tuple(tuple(u, int), v), u)) = spawn{(super:)Run()}
Main()<suspends>:void =
    P := child(int, string){A := (7, "q"), B := 9}
    R := P.Kick().Await()
    Print("{R(0)(0)} {R(0)(1)} {R(1)}")
    P3 := child3(string){A := holder(string){H := "h"}, B := 9}
    R3 := P3.Kick().Await()
    Print("{R3(0).H} {R3(1)}")
    P4 := child4(int, string){A := ((1, 2), "s"), B := 3}
    R4 := P4.Kick().Await()
    Print("{R4(0)(0)(0)} {R4(0)(1)} {R4(1)}")
