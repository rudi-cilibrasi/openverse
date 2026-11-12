vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
worker:=class<allocates>:
    Item:car
    var Calls:int=0
    Fetch(X:vehicle)<transacts>:car=
        set Calls+=1
        set X.N+=1
        Item
Pick(W:worker,M:counter)<transacts>:worker=
    set M.N+=1
    W
Build(W:worker,M:counter)<transacts>:type{_(:car)<transacts>:vehicle}=Pick(W,M).Fetch
Main():void=
    C:=car{}
    W:=worker{Item:=C}
    M:=counter{}
    F:=Build(W,M)
    set C.N=4
    R:=F(C)
    if:
        F(C)
        false?
    then:
        Print("bad")
    else:
        Print("rollback {C.N} {W.Calls} {M.N}")
    Print("precise {C.Name} result {R.N}")
