# expect: not in a failure context
Main():void =
    O:?int = option{1 > 0}
    Y := O?
