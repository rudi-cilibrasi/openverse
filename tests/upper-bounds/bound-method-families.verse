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
Collect(B:t where t:subtype(box(car)))<reads>:[]car=for(X:=B.Vals()):X
Main()<transacts>:void=
    A:=car{Name:="a"}
    B:=car{Name:="b",N:=9}
    Rows:=Collect(box(car){Item:=A})
    for(X:Rows):
        Print("box {X.Name} {Read(X)}")
    for(X:=pair(car){L:=A,R:=B}.Vals()):
        Print("pair {X.Name} {Read(X)}")
    Print("counter {counter{}.Vals()}")
