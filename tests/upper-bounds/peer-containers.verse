Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    AB:[]rational=array{1}
    AV:[]int=array{7}
    A:=Upper(AB,AV)
    if(N:=A[0],N=7):Print("array peer")
    OB:?rational=option{1}
    OV:?int=option{8}
    O:=Upper(OB,OV)
    if(N:=O?,N=8):Print("option peer")
    MB:[int]rational=map{1=>1}
    MV:[int]int=map{1=>9}
    M:=Upper(MB,MV)
    if(N:=M[1],N=9):Print("map peer")
    TB:tuple(rational,string)=(1,"base")
    TV:tuple(int,string)=(10,"tag")
    T:=Upper(TB,TV)
    if(T(0)=10):Print("tuple peer {T(1)}")
