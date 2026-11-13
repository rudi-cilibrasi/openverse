vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
Read(X:t where t:subtype(vehicle))<reads>:int=X.N
box(a:subtype(vehicle)):=class<computes>:
    Item:a
    Vals()<reads>:a=Item|Item
pair(a:subtype(vehicle)):=class<computes>:
    L:a
    R:a
    Vals()<reads>:a=L|R
counter:=class<computes>:
    Vals()<computes>:int=42
probe:=class<allocates>{var N:int=0}
Take(B:t,C:probe where t:subtype(box(car)))<transacts>:t=
    set C.N+=1
    B
Collect(B:t,C:probe where t:subtype(box(car)))<transacts>:[]car=for(X:=Take(B,C).Vals()):X
Main()<transacts>:void=
    A:=car{Name:="a"}
    B:=car{Name:="b",N:=9}
    C:=probe{}
    Rows:=Collect(box(car){Item:=A},C)
    for(X:Rows):
        Print("box {X.Name} {Read(X)}")
    Print("calls {C.N}")
    for(X:=pair(car){L:=A,R:=B}.Vals()):
        Print("pair {X.Name} {Read(X)}")
    Print("counter {counter{}.Vals()}")
