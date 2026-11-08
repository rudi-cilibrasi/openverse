# expect: spawn in a generic function is not supported yet
W(X:t where t:type)<suspends>:t = X
H(X:t where t:type)<suspends>:void =
    spawn{W(X)}
Main()<suspends>:void = H(1)
