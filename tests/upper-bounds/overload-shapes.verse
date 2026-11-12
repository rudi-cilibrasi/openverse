vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
Pair(X:tuple(t,int) where t:subtype(car))<computes>:int=10+X(1)
Pair(X:tuple(t,int) where t:subtype(truck))<computes>:int=20+X(1)
Named(?X:t,?N:int=7 where t:subtype(car))<computes>:int=10+N
Named(?X:t,?N:int=7 where t:subtype(truck))<computes>:int=20+N
Peer(X:u where t:subtype(car),u:subtype(t))<computes>:int=3
Peer(X:u where t:subtype(truck),u:subtype(t))<computes>:int=4
Main():void=
    Print("tuple {Pair(car{},1)} {Pair((truck{},2))}")
    Print("named {Named(?X:=car{})} {Named(?N:=9,?X:=truck{})}")
    Print("peer {Peer(car{})} {Peer(truck{})}")
