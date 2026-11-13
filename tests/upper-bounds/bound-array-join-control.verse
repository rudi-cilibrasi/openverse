vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="car"}
truck:=class<computes>(vehicle){Name:string="truck"}
Join(A:[]vehicle,B:[]vehicle)<computes>:[]vehicle=A+B
Infer(A:[]vehicle,B:[]vehicle)<computes>:[]vehicle=
    R:=A+B
    R
Nested(A:[][]vehicle,B:[][]vehicle)<computes>:[][]vehicle=
    R:=A+B
    R
Numbers(A:[]rational,B:[]rational)<computes>:[]rational=
    R:=A+B
    R
Main():void=
    C:=car{}
    T:=truck{N:=9}
    R:=Join(array{C},array{T})
    I:=Infer(array{T},array{C})
    if(X:=R[0],Y:=R[1],P:=I[0],Q:=I[1])then Print("joined {X.N} {Y.N} inferred {P.N} {Q.N}")
    EC:[]car=array{}
    ET:[]truck=array{}
    Print("empty {Join(EC,ET).Length}")
    N:=Nested(array{array{C}},array{array{T}})
    if(X:=N[0],Y:=N[1],P:=X[0],Q:=Y[0])then Print("nested {N.Length} {P.N} {Q.N}")
    Two:rational=2
    V:=Numbers(array{1},array{Two})
    if(X:=V[0],Y:=V[1],X=1,Y=2)then Print("numeric elements {V.Length}")
