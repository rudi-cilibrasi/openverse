# a spawned call of an override that reads its class's type parameters from
# its receiver, with an argument that has no type of its own (array{}, false)
# where the parameter's type mentions them (#209): no witness gives them, so
# the task's root reads them off the receiver's type (arrJ(int) gives a :=
# int; optJ(t, s), in code generic over t and s, gives them as t and s)
job(t:type) := class<abstract>:
    Run()<suspends>:t
    Put(X:t, Y:u where u:type)<suspends>:tuple(u, t)
arrJ(a:type) := class(job([]a)):
    Run<override>()<suspends>:[]a = array{}
    Put<override>(X:[]a, Y:u where u:type)<suspends>:tuple(u, []a) =
        Sleep(0.1)
        (Y, X)
optJ(a:type, b:type) := class(job(?tuple(a, b))):
    B:b
    Run<override>()<suspends>:?tuple(a, b) = false
    Put<override>(X:?tuple(a, b), Y:u where u:type)<suspends>:tuple(u, ?tuple(a, b)) =
        Sleep(0.1)
        (Y, X)
G(P:arrJ(t), X:t where t:type)<suspends>:int =
    T := spawn{P.Put(array{}, X)}
    U := spawn{P.Put(array{X, X}, 0)}
    T.Await()(1).Length + U.Await()(1).Length
H(P:optJ(t, s), Y:s where t:type, s:type)<suspends>:logic =
    T := spawn{P.Put(false, Y)}
    O := T.Await()(1)
    if (O?) then false else true
Main()<suspends>:void =
    P := arrJ(int){}
    T := spawn{P.Put(array{}, 1)}
    Print("{T.Await()(0)} {T.Await()(1).Length}")
    Print("{G(arrJ(int){}, 3)} {G(arrJ(string){}, "s")}")
    R := H(optJ(int, string){B := "b"}, "y")
    if (R?) then Print("none")
