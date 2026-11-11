# expect: ?N is given twice
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=Seed)<suspends>:void=Print("body {N}")
Start(P:base(t) where t:type):task(void)=spawn{P.Go(?N:=1,?N:=2)}
Main():void=
    T:=Start(ib{})
    Print("bad")
