# expect: spawn in a generic function of a call whose result type mentions its type parameters
W(X:t where t:type)<suspends>:t = X
H(X:t where t:type)<suspends>:void =
    spawn{W(X)}
Main()<suspends>:void = H(1)
