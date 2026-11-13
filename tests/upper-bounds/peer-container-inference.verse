Choose(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
vehicle:=class<computes>{Speed:int=5}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
Main():void=
    A:[]int=array{7}
    B:[]rational=array{1}
    R:=Choose(A,B)
    if(V:=R[0],V=7):Print("inferred array 7")
    O:?int=option{8}
    P:?rational=false
    S:=Choose(O,P)
    if(V:=S?,V=8):Print("inferred option 8")
    M:[int]int=map{2=>9}
    N:[int]rational=map{}
    T:=Choose(M,N)
    if(V:=T[2],V=9):Print("inferred map 9")
    U:tuple(int,string)=(10,"tag")
    W:tuple(rational,string)=(1,"base")
    Pair:=Choose(U,W)
    if(Pair(0)=10):Print("inferred tuple 10 {Pair(1)}")
    AC:[]car=array{car{Speed:=12}}
    AT:[]truck=array{truck{}}
    Vehicles:=Choose(AC,AT)
    if(V:=Vehicles[0]):Print("inferred class {V.Speed}")
    NI:[]?tuple(int,string)=array{option{(13,"nested")}}
    NR:[]?tuple(rational,string)=array{}
    Nested:=Choose(NI,NR)
    if(O2:=Nested[0],T2:=O2?,T2(0)=13):Print("inferred nested 13 {T2(1)}")
