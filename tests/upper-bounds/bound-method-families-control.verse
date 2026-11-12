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
Collect(B:box)<reads>:[]car=for(X:=B.Vals()):X
Main()<transacts>:void=
    A:=car{Name:="a"}
    B:=car{Name:="b",N:=9}
    Rows:=Collect(box{Item:=A})
    for(X:Rows):
        Print("box {X.Name} {Read(X)}")
    for(X:=pair{L:=A,R:=B}.Vals()):
        Print("pair {X.Name} {Read(X)}")
    Print("counter {counter{}.Vals()}")
