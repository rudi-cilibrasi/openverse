# expect: spawn{…} takes a call of a <suspends> function
F():int = 1
Main()<suspends>:void =
    spawn{F()}
