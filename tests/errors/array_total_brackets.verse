# expect: 3:39: RemoveAllElements cannot fail: call it with A.RemoveAllElements(…)
Main():void =
    if (B := array{1}.RemoveAllElements[1]) then Print("x")
