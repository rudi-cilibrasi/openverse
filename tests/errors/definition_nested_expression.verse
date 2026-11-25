# expect: unknown identifier 'Y'
# A definition whose value is a definition defines both (#724,
# tests/verse/definition_chain); one deeper in an expression binds nothing
# after it yet.
Main():void =
    X:int = (Y := 4) + 1
    Print("{X} {Y}")
