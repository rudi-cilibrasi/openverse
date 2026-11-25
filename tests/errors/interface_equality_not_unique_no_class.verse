# expect: must be comparable, and shape is a class (only <unique> classes are comparable, by identity)
# An interface that no class implements is comparable only when it is
# <unique> (#724, tests/verse/unique_interface_no_class).
shape := interface:
    Sides():int
Same(A:shape, B:shape):logic = if (A = B) then true else false
Main():void =
    Print("compiled")
