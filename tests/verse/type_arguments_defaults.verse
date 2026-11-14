# A type given as an argument (FalseOption(t:type):?t, the Book's tests,
# ParametricTypes.versetest 613-624) in a method's parameter's default, as
# in a function's, and in a struct's field's default, as in a class's.
FalseOption(t:type)<computes>:?t = false
holder := struct:
    Value:?int = FalseOption(int)
box := class:
    Value:?string = FalseOption(string)
    Get(?Or:?float = FalseOption(float)):?float = Or
Pick(?Or:?int = FalseOption(int)):?int = Or
Main():void =
    if (holder{}.Value?) then Print("some") else Print("none")
    if (box{}.Value?) then Print("some") else Print("none")
    if (box{}.Get()?) then Print("some") else Print("none")
    if (V := box{}.Get(?Or := option{1.5})?) then Print("{V}")
    if (Pick()?) then Print("some") else Print("none")
