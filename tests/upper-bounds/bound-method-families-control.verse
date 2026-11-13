vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
Read(X:car)<reads>:int=X.N
box:=class<computes>:
    Item:car
    Vals()<reads>:car=Item|Item
pair:=class<computes>:
    L:car
    R:car
    Vals()<reads>:car=L|R
counter:=class<computes>:
    Vals()<computes>:int=42
probe:=class<allocates>{var N:int=0}
Take(B:box,C:probe)<transacts>:box=
    set C.N+=1
    B
Collect(B:box,C:probe)<transacts>:[]car=for(X:=Take(B,C).Vals()):X
Main()<transacts>:void=
    A:=car{Name:="a"}
    B:=car{Name:="b",N:=9}
    C:=probe{}
    Rows:=Collect(box{Item:=A},C)
    for(X:Rows):
        Print("box {X.Name} {Read(X)}")
    Print("calls {C.N}")
    for(X:=pair{L:=A,R:=B}.Vals()):
        Print("pair {X.Name} {Read(X)}")
    Print("counter {counter{}.Vals()}")
