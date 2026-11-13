# expect: the type of an empty array{} must be given
# An empty array{} is the empty value of the other operand's type when that
# type has it; an int does not.
Main():void =
    if (array{} = 0) then Print("equal")
