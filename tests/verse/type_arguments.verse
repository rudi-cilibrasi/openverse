# A type given as an argument and used as a type (Book of Verse tests,
# ParametricTypes.versetest 613-624, TypeParam.versetest 57-60): the function is
# generic over it, and the call writes its type argument.
FalseOption(t:type):?t = false
EmptyArray(t:type):[]t = array{}
Pair(t:type, X:t, Y:t):tuple(t, t) = (X, Y)
c := class:
    N:int = 3
Main():void =
    X := FalseOption(int)
    if (not X?):
        Print("empty")
    Y := EmptyArray(string)
    Print(ToString(Y.Length))
    P := Pair(int, 1, 2)
    Print(ToString(P(0) + P(1)))
    Z := FalseOption(c)
    if (not Z?):
        Print("no c")
    if (FalseOption(int) = FalseOption(logic)):
        Print("equal")
