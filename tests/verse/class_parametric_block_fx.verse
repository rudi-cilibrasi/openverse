# a parametric class's block: has the effects of its code (#39): this one
# only prints; its explicit <computes> contract admits pure construction
tagged(t:type) := class<computes>:
    Value:t
    block:
        Print("made one")
Make(X:t where t:type)<computes>:tagged(t) = tagged(t){Value := X}
Main():void =
    T := Make(3)
    Print("{T.Value}")
