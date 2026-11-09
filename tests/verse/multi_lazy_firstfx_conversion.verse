# values that convert to the generator's result type (false and option{N} as ?int), where the first success is taken (#246 step 2, review)
Opts(N:int)<transacts><decides>:?int =
    N < 4
    Print("at {N}")
    false | option{N} | Opts[N + 1]
Main():void =
    if (O := Opts[0], V := O?, V > 1) then Print("v {V}")
