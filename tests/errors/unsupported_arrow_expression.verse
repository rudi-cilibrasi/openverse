# expect: a top-level definition must start at column 0
# The operands can parse; the unsupported arrow expression must still fail.
Main():void =
    X := 7
    F := (X) => X + 1
    Print(F(X))
