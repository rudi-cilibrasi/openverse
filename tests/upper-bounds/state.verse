vehicle:=class<allocates>:
    var N:int=0
    var Items:[]int=array{1}
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string="car"}
Touch(X:t where t:subtype(vehicle))<transacts>:t=
    Print("touch")
    set X.N+=1
    X
BindN(X:t where t:subtype(vehicle))<computes>:type{_()<reads>:int}=X.ReadN
SetPath(A:t,B:t where t:subtype(vehicle))<transacts>:void=
    var X:t=A
    if(set X.Items[if(set X=B,true?)then 0 else 1]=7):Print("path")
Main():void=
    A:=car{Name:="a",Items:=array{1}}
    B:=car{Name:="b",N:=10,Items:=array{2}}
    Returned:=Touch(A)
    Print("identity {Returned.Name} {A.N}")
    if(Touch(A),false?)then Print("bad")else Print("rolled")
    Print("rollback {A.N}")
    Live:=BindN(A)
    set A.N=4
    Print("live {Live()}")
    SetPath(A,B)
    if(AV:=A.Items[0],BV:=B.Items[0]):Print("path values {AV} {BV}")
