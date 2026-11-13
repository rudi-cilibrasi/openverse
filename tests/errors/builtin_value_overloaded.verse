# expect: 4:9: the built-in Abs cannot be used as a value
# Abs is of an int or of a float: overloaded, it is no value, as an overloaded function is not.
Main():void =
    F := Abs
