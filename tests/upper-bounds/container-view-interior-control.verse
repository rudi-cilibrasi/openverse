vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Index(V:vehicle,C:counter)<transacts>:int=
    set V.N=20
    set C.N=C.N*10+1
    0
Key(V:vehicle,C:counter)<transacts>:int=
    set V.N=20
    set C.N=C.N*10+1
    1
Rhs(V:vehicle,C:counter)<transacts>:int=
    set V.N=100
    set C.N=C.N*10+2
    3
Array(A:[]vehicle,V:vehicle,C:counter)<transacts><decides>:int=
    set A[Index(V,C)].N+=Rhs(V,C)
    A[0].N
Option(A:?vehicle,V:vehicle,C:counter)<transacts><decides>:int=
    set A?.N+=Rhs(V,C)
    A?.N
Map(A:[int]vehicle,V:vehicle,C:counter)<transacts><decides>:int=
    set A[Key(V,C)].N+=Rhs(V,C)
    A[1].N
Main():void=
    V:=car{}
    C:=counter{}
    if(R:=Array[array{V},V,C])then Print("array {R} {C.N} {V.N}")else Print("bad")
    if(Array[array{V},V,C],false?)then Print("bad")else Print("rollback {V.N} {C.N}")
    set V.N=7
    set C.N=0
    if(R:=Option[option{V},V,C])then Print("option {R} {C.N} {V.N}")else Print("bad")
    set V.N=7
    set C.N=0
    if(R:=Map[map{1=>V},V,C])then Print("map {R} {C.N} {V.N} {V.Name}")else Print("bad")
