vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){}
node(a:type):=class<computes>{Child:a}
child(a:type):=class<computes>(node(a)){}
holder(t:subtype(node(u)),u:subtype(vehicle)):=class<computes>:
    X:t
    Touch()<transacts>:void=set X.Child.N+=1
Main():void=
    A:=car{}
    H:=holder(child(car),car){X:=child(car){Child:=A}}
    H.Touch()
    Print("nested {A.N}")
