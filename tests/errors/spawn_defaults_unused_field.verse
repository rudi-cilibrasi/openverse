# expect: expected int, found string
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?N:int="bad")<suspends>:void=Print("body {N}")
AsBase(P:base(t) where t:type):base(t)=P
unused := struct:
    T:task(void)=spawn{AsBase(ib{}).Go()}
Main():void=Print("unused")
