vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){}
holder(t:subtype(vehicle)):=class<computes>:
    X:t
    Touch()<transacts>:void=set X.N+=1
Main():void=
    A:=car{}
    H:=holder(car){X:=A}
    H.Touch()
    Print("interior {A.N}")
