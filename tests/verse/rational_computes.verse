# the rational helpers are <computes> (#116 review): a function without <writes> may divide and order
Half(X:int)<computes><decides>:rational = X / 2
Below(R:rational)<reads><decides>:void = R < 1
Main():void =
    if (R := Half[1], Below[R]) then Print("ok")
