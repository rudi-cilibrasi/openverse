vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
Collect(A:[]a,Seed:a where a:type)<computes>:[]a=for(V:A):V
Indexed(A:[]int)<computes>:[]int=for(I->V:A):I+V
Values(M:[int]car)<computes>:[]car=for(V:M):V
Keys(M:[int]car)<computes>:[]int=for(K->V:M):K
Chars(S:string)<computes>:[]char=for(C:S):C
Grid(A:[]int,B:[]int)<computes>:[]int=for(X:A,Y:B):X*10+Y
Main():void=
    A:=car{Name:="a"}
    B:=car{Name:="b"}
    R:=Collect(array{A,B},A)
    if(X:=R[0],Y:=R[1])then Print("array {R.Length} {X.Name} {Y.Name}")
    Empty:[]car=array{}
    Print("empty {Collect(Empty,A).Length}")
    I:=Indexed(array{4,6})
    if(X:=I[0],Y:=I[1])then Print("indexed {X} {Y}")
    M:=map{9=>A,7=>B}
    V:=Values(M)
    K:=Keys(M)
    if(X:=V[0],Y:=V[1],J:=K[0],L:=K[1])then Print("map {J} {X.Name} {L} {Y.Name}")
    Print("chars {Chars("ab").Length}")
    G:=Grid(array{1,2},array{3,4})
    if(X:=G[0],Y:=G[3])then Print("grid {G.Length} {X} {Y}")
