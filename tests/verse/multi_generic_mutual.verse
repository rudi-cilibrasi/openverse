# A typed lazy stack keeps each member's parameter permutation and annotations.
cell := class { var N:int=0 }
Emit(X:t,Y:u,N:int where t:type,u:type)<transacts>:tuple(t,u,int) =
    Print("value {N}")
    (X,Y,N)
A(X:a,Y:b,N:int,H:cell where a:type,b:subtype(comparable))<transacts><decides>:tuple(a,b,int) =
    N>=0
    set H.N+=1
    Print("A {N}")
    if(N>0)then (Emit(X,Y,10*N) | B[(Y,X,N-1,H)] | Emit(X,Y,10*N+1))else Emit(X,Y,0)
B(Y:k,X:v,N:int,H:cell,?E:[]v=Concatenate() where k:subtype(comparable),v:type)<transacts><decides>:tuple(v,k,int) =
    N>=0
    set H.N+=1
    Print("B {N}")
    M:[k]v=map{Y=>X}
    T:tuple(v,k)=(X,Y)
    if(N>0)then (Emit(T(0),T(1),10*N+2) | C[(T,N-1,H)] | Emit(T(0),T(1),10*N+3))else Emit(X,Y,2)
C(Z:tuple(c,d),N:int,H:cell where c:type,d:subtype(comparable))<transacts><decides>:tuple(c,d,int) =
    N>=0
    set H.N+=1
    Print("C {N}")
    E:[]c=Concatenate()
    if(N>0)then (Emit(Z(0),Z(1),10*N+4) | A[Z(0),Z(1),N-1,H] | Emit(Z(0),Z(1),10*N+5))else Emit(Z(0),Z(1),4)
Run(X:b,Y:a,W:w where a:subtype(comparable),b:type,w:type):?tuple(b,a,int) =
    F:=cell{}
    var Seen:int=0
    Result:=option{V:=B[(Y,X,2,F)];E:[]w=Concatenate();set Seen+=V(2);V(2)=0;V}
    Print("state {F.N} {Seen}")
    Result
Main():void =
    H:=cell{}
    for(V:=A[(7,"s",2,H)],V(2)>4): Print("got {V(0)} {V(1)} {V(2)}")
    Print("visits {H.N}")
    if(V:=Run("s",7,option{"w"})?)then Print("first {V(0)} {V(1)} {V(2)}")else Print("none")
    F:=cell{}
    if(V:=C[((7,"s"),2,F)],V(2)<0)then Print("unexpected")else Print("none")
    Print("failed {F.N}")
