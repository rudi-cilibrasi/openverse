# expect: Make constructs tagged, whose block: (in tagged), which has the effect <writes>
tagged(t:type) := class:
    var Value:t
    block:
        set Value = Value
Make(X:t where t:type)<computes>:tagged(t) = tagged(t){Value := X}
Main():void = Print("x")
