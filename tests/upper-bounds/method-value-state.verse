vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
worker(a:subtype(vehicle)):=class<allocates>:
    Item:a
    var Calls:int=0
    Fetch(X:vehicle)<transacts>:a=
        set Calls+=1
        set X.N+=1
        Item
Pick(W:worker(t),M:counter where t:subtype(vehicle))<transacts>:worker(t)=
    set M.N+=1
    W
Build(W:worker(t),M:counter where t:subtype(vehicle))<transacts>:type{_(:t)<transacts>:vehicle}=Pick(W,M).Fetch
Main():void=
    C:=car{}
    W:=worker(car){Item:=C}
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
