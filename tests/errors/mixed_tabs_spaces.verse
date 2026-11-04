# expect: 6:8: inconsistent use of tabs and spaces
# The block of the if is indented with two tabs, the next line with 8 spaces.
Main():void =
	if (1 > 0):
		Print("a")
        Print("b")
