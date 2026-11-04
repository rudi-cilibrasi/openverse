# expect: break is only allowed inside loop
Main():void =
    for (X := 1..3) { break }
