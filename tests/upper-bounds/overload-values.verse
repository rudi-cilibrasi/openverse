vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
Pick(X:t where t:subtype(car))<computes>:int=1
Pick(X:t where t:subtype(truck))<computes>:int=2
ForCar(X:t where t:subtype(car))<computes>:int=Pick(X)
ForTruck(X:t where t:subtype(truck))<computes>:int=Pick(X)
router:=class<computes>:
    Select(X:t where t:subtype(car))<computes>:int=3
    Select(X:t where t:subtype(truck))<computes>:int=4
    ForCar(X:t where t:subtype(car))<computes>:int=Select(X)
child:=class<computes>(router):
    Select<override>(X:u where u:subtype(car))<computes>:int=8
Narrow(X:t where t:subtype(car))<computes>:int=Pick(X)
Main():void=
    C:type{_(:car)<computes>:int}=ForCar
    T:type{_(:truck)<computes>:int}=ForTruck
    R:=router{}
    M:type{_(:car)<computes>:int}=R.ForCar
    Print("values {C(car{})} {T(truck{})} {M(car{})}")
    Print("methods {R.Select(car{})} {R.Select(truck{})} {Narrow(car{})}")
    S:=child{}
    Print("override overload {S.Select(car{})} {S.Select(truck{})}")
