# formerly refused; generic functions with task roots are specialised (#174)
W(X:t where t:type)<suspends>:t = X
H(X:t where t:type)<suspends>:void =
    spawn{W(X)}
Main()<suspends>:void = H(1)
