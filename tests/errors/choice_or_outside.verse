# expect: 4:18: a choice (a | b) has several values, so it must be in a failure context that takes them
# The right of or is no failure context: its choice's values are the or's, which something must take (#283).
Main():void =
    X := O? or (1 | 2)
    Print("{X}")
O:?int = false
