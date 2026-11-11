# expect: branch cannot be in a loop or for body
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=block{branch{Print("default")};Seed})<suspends>:void=Print("body {N}")
Start(P:base(t) where t:type)<suspends>:void=
    for(I:=0|1):
        T:=spawn{P.Go()}
        Print("bad")
Main()<suspends>:void=Start(ib{})
