# expect: 4:24: break cannot leave an if condition or first{…} that has a choice
Main():void =
    loop:
        if (X := 1 | 2, break) then Print("x")
        break
