# a return in the clauses after an effect-free generator, where the first success is taken: the loop runs them in the function, so it leaves it (#246)
H(N:int)<computes><decides>:int = N | H[N + 1]
K():int =
    if (X := H[0], if (X = 2) then return 42 else true, X = 3) then 7 else 8
Main():void = Print("{K()}")
