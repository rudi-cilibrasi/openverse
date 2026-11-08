# expect: a spawned call whose arguments' types mention the function's type parameters
W(X:t where t:type)<suspends>:int = 1
H(X:t where t:type)<suspends>:void =
    T := spawn{W(X)}
Main()<suspends>:void = H(1)
