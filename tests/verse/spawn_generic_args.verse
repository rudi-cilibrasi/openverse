# formerly refused; generic functions with task roots are specialised (#174)
W(X:t where t:type)<suspends>:int = 1
H(X:t where t:type)<suspends>:void =
    T := spawn{W(X)}
Main()<suspends>:void = H(1)
