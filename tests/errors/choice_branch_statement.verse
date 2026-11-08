# expect: 3:28: a choice (a | b) has several values, so it must be in a failure context that takes them
Main():void =
    Y := if (1 > 0) then (1 | 2) else 3
    Print("{Y}")
