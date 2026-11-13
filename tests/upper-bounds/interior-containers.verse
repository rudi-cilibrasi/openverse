vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){}
holder(t:subtype(vehicle)):=class<computes>:
    A:[]t
    M:[int]t
    O:?t
    Touch()<transacts>:void=
        if(set A[0].N+=1):{}
        if(set M[1].N+=2):{}
        if(set O?.N+=4):{}
Main():void=
    A:=car{}
    H:=holder(car){A:=array{A},M:=map{1=>A},O:=option{A}}
    H.Touch()
    Print("containers {A.N}")
