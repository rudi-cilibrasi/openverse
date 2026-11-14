# A built-in function named as a value in a struct's field's default, as in
# a class's (the Book's tests pass Sin to a parameter F(:float):float).
waves := struct:
    Wave:type{_(:float):float} = Sin
    Mask:type{_(:int, :int):int} = BitAnd
shapes := class:
    Wave:type{_(:float):float} = Cos
Main():void =
    W := waves{}
    Print("{W.Wave(0.0)} {W.Mask(6, 3)} {shapes{}.Wave(0.0)}")
