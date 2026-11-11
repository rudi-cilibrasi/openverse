# expect: effect <writes>
base(t:type) := class:
    Go(?N:int=0)<suspends><computes>:void=Print("base")
ib := class(base(int)):
    var Calls:int=0
    Go<override>(?N:int=block{set Calls+=1;Calls})<suspends><computes>:void=Print("body {N}")
Start(P:base(t) where t:type)<computes>:task(void)=spawn{P.Go()}
Main():void=
    T:=Start(ib{})
    Print("bad")
