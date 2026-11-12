vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Both(A:[]int,B:[]int)<computes>:[]int=A+B
Left(A:[]int)<computes>:[]int=A+array{9}
Right(A:[]int)<computes>:[]int=array{8}+A
Text(A:string,B:string)<computes>:string=A+B
Precise(A:[]a,B:[]a,Seed:a where a:type)<computes>:[]a=A+B
Join(A:[]car,B:[]vehicle)<computes>:[]vehicle=A+B
Take(A:[]int,C:counter,Digit:int)<transacts>:[]int=
    set C.N=C.N*10+Digit
    A
Ordered(A:[]int,B:[]int,C:counter)<transacts>:[]int=Take(A,C,1)+Take(B,C,2)
Main()<transacts>:void=
    R:=Both(array{1,2},array{3})
    L:=Left(array{1,2})
    Q:=Right(array{1,2})
    if(X:=R[2],Y:=L[2],Z:=Q[0])then Print("concat {R.Length} {X} {Y} {Z}")
    Empty:[]int=array{}
    Print("empty {Both(Empty,Empty).Length}")
    Print("text {Text("ab","cd")}")
    A:=car{Name:="a"}
    B:=car{Name:="b",N:=9}
    P:=Precise(array{A},array{B},A)
    J:=Join(array{A},array{vehicle{N:=11}})
    if(X:=P[0],Y:=P[1],Z:=J[1])then Print("precise {X.Name} {Y.Name} joined {Z.N}")
    C:=counter{}
    O:=Ordered(array{4},array{5},C)
    if(X:=O[0],Y:=O[1])then Print("ordered {X} {Y} {C.N}")
    if(Ordered(array{6},array{7},C),false?)then Print("bad")else Print("rollback {C.N}")
