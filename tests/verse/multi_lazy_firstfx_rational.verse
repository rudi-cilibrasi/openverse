# int values of a generator returning rational, where the first success is taken (#246 step 2, review)
Ratio(N:int)<transacts><decides>:rational =
    N < 3
    Print("r {N}")
    N | Ratio[N + 1]
Main():void =
    if (R := Ratio[0], R > 1/1) then Print("rat {Floor(R)}")
