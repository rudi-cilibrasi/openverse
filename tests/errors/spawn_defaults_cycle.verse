# expect: uses itself
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?N:int=block{T:=spawn{Go()};3})<suspends>:void=Print("body {N}")
Start(P:base(t) where t:type):task(void)=spawn{P.Go()}
Main():void=
    T:=Start(ib{})
    Print("bad")
