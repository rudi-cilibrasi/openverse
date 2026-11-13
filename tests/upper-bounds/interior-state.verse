vehicle:=class<allocates>:
    var N:int=0
    var Items:[]int=array{1}
car:=class<allocates>(vehicle){Name:string="a"}
holder(t:subtype(vehicle)):=class<allocates>:
    var X:t
    Other:t
    Index()<transacts>:int=
        Print("index")
        set X=Other
        0
    Rhs(After:t)<transacts>:int=
        set X=After
        set X.Items=array{50,60}
        set X.N=90
        Print("rhs")
        7
    Write(After:t)<transacts>:void=
        if(set X.Items[Index()]+=Rhs(After)):Print("set")
    Precise()<reads>:t=X
Main():void=
    A:=car{Items:=array{1,10}}
    B:=car{Name:="b",Items:=array{2,20}}
    H:=holder(car){X:=A,Other:=B}
    H.Write(A)
    if(A0:=A.Items[0],A1:=A.Items[1],B0:=B.Items[0],B1:=B.Items[1]):
        Print("values {H.Precise().Name} {A.N} {B.N} {A0} {A1} {B0} {B1}")
    if(H.Write(A),false?)then Print("bad")else Print("rolled")
    if(A0:=A.Items[0],A1:=A.Items[1],B0:=B.Items[0],B1:=B.Items[1]):
        Print("after {H.Precise().Name} {A.N} {B.N} {A0} {A1} {B0} {B1}")
