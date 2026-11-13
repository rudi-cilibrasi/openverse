vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
counter:=class:
    var N:int=0
    Car():car=
        set N+=1
        Print("car {N}")
        car{}
    Truck():truck=
        set N+=1
        Print("truck {N}")
        truck{}
Pick(X:t,?N:int=7 where t:subtype(car))<computes>:int=10+N
Pick(X:t,?N:int=9 where t:subtype(truck))<computes>:int=20+N
Main():void=
    H:=counter{}
    Print("selected {Pick(H.Car())} {Pick(H.Truck())}")
    Print("count {H.N}")
