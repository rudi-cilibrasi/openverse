# a spawned call's argument with no type of its own takes the callee's
# parameter type at its type arguments (#174)
Count(Xs:[]u where u:type)<suspends>:int =
    Sleep(1.0)
    Xs.Length
Main()<suspends>:void =
    E:[]int = array{}
    T := spawn{Count(E)}
    U:task(int) = spawn{Count(array{1, 2, 3})}
    Print("{T.Await()} {U.Await()}")
