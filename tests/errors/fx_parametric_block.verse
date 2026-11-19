# expect: Make constructs tagged, whose block: (in tagged), which has the effect <writes>
# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
tagged(t:type) := class:
    var Value:t
    block:
        set Value = Value
Make(X:t where t:type)<computes>:tagged(t) = tagged(t){Value := X}
Main():void = Print("x")
