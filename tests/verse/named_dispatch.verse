# named arguments to a method dispatched on the receiver's class: evaluated
# once each, positional then named as written, and passed to every
# implementation; omitted ones take the running implementation's default

shape := class<abstract>:
    Scale(K:int, ?By:int = 1, ?Plus:int = 0):int
square := class(shape):
    Side:int
    Scale<override>(K:int, ?By:int = 1, ?Plus:int = 0):int = Side * K * By + Plus
circle := class(shape):
    R:int
    # (its own default for Plus)
    Scale<override>(K:int, ?By:int = 1, ?Plus:int = 100):int = 3 * R * K * By + Plus
Note(S:string, X:int):int =
    Print(S)
    X
Main():void =
    Ss:[]shape = array{square{Side := 2}, circle{R := 1}}
    for (S : Ss):
        Print("{S.Scale(1)} {S.Scale(2, ?By := 3)} {S.Scale(1, ?Plus := 5, ?By := 2)}")
    if (S0 := Ss[0]):
        # arguments evaluated once each, in the order written
        Print("{S0.Scale(Note("k", 1), ?Plus := Note("plus", 1), ?By := Note("by", 2))}")
