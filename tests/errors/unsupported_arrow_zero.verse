# expect: a top-level definition must start at column 0
# Rejection of an arrow expression; no future lambda grammar is implied.
Main():void =
    F := () => 7
    Print(F())
