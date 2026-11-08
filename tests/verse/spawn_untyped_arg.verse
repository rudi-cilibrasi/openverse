# a spawned argument with no type of its own, in a generic function: the callee's parameter type at its type arguments (#174)
Both(X:?t, Y:t, Z:[]t where t:type)<suspends>:int =
    Sleep(0.5)
    Z.Length + (if (X?) then 1 else 0)
Gen(Y:u where u:type)<suspends>:int =
    T := spawn{Both(false, Y, array{})}
    T.Await()
Main()<suspends>:void =
    T := spawn{Both(false, 3, array{})}
    Print("{T.Await()}")
    Print("{Gen("s")}")
    Print("{Gen(array{1})}")
