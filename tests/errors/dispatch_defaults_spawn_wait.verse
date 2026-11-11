# expect: the arguments of a spawned call cannot suspend
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?N:int=block{Sleep(0.01);3})<suspends>:void=Print("body {N}")
Start(P:base(t) where t:type)<suspends>:void=
    T:=spawn{P.Go()}
    Print("spawned")
    Sleep(0.2)
Main()<suspends>:void=Start(ib{})
