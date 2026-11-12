Round(A:rational,B:rational)<computes><decides>:tuple(int,int)=(Floor(A/B),Ceil(A/B))
Main():void=
    if(A:=7/2,B:=-3/2,R:=Round[A,B]):Print("{R(0)} {R(1)}")
    if(A:=7/2,R:=Round[A,0])then Print("bad")else Print("zero")
