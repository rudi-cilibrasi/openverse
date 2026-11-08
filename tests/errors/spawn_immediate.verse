# expect: spawn is supported only in a <suspends> function for now
W()<suspends>:void = Sleep(1.0)
Main():void =
    spawn{W()}
