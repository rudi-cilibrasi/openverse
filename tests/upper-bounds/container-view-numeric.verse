counter:=class<allocates>{var N:int=0}
Tick(C:counter,V:int)<transacts>:int=
    set C.N+=1
    Print("tick {C.N}")
    V
Half(R:rational)<computes><decides>:int=Floor[R/2]
Index(A:t,C:counter where t:subtype([]rational))<transacts><decides>:int=Half[A[Tick(C,1)]]
Nested(A:t where t:subtype([][]rational))<computes><decides>:int=Half[A[1][0]]
Project(T:t where t:subtype(tuple(rational,[]rational)))<computes><decides>:int=Half[T(0)]+Half[T(1)[0]]
Query(O:t where t:subtype(?rational))<computes><decides>:int=Half[O?]
Lookup(M:t where t:subtype([int]rational))<computes><decides>:int=Half[M[2]]
Main():void=
    C:=counter{}
    A:[]int=array{3,7}
    if(X:=Index[A,C]):Print("index {X}")
    if(Index[array{5},C])then Print("bad")else Print("rolled index {C.N}")
    N:[][]int=array{array{1},array{9,2}}
    if(X:=Nested[N]):Print("nested {X}")
    T:tuple(int,[]int)=(5,array{11})
    if(X:=Project[T]):Print("tuple {X}")
    O:?int=option{13}
    if(X:=Query[O]):Print("option {X}")
    E:?int=false
    if(Query[E])then Print("bad")else Print("empty option")
    M:[int]int=map{2=>15}
    if(X:=Lookup[M]):Print("map {X}")
