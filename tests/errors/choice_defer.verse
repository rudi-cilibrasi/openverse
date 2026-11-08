# expect: 3:20: defer: cannot be a clause of an if condition or first{…} that has a choice
Main():void =
    if (X := 1 | 2, defer { Print("d") }, X > 1) then Print("x")
