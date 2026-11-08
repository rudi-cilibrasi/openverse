# expect: the arguments of a spawned call cannot suspend
G()<suspends>:int = 1
W(X:int)<suspends>:void = Sleep(1.0)
Main()<suspends>:void =
    spawn{W(G())}
