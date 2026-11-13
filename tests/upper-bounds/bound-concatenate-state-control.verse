vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Take(X:t,C:counter,Digit:int where t:type)<transacts>:t=
    set C.N=C.N*10+Digit
    X
Flatten(A:[][]vehicle,C:counter)<transacts>:[]vehicle=Concatenate(Take(A,C,1))
Arrays(A:[]vehicle,B:[]vehicle,C:counter)<transacts>:[]vehicle=Concatenate(Take(A,C,1),Take(B,C,2))
Maps(A:[int]vehicle,B:[int]vehicle,C:counter)<transacts>:[int]vehicle=ConcatenateMaps(Take(A,C,1),Take(B,C,2))
Fail(X:t,C:counter where t:type)<transacts><decides>:t=
    set C.N=C.N*10+9
    false?
    X
Attempt(A:[][]vehicle,C:counter)<transacts>:?[]vehicle=option{Concatenate(Fail[A,C])}
Wait(A:[][]vehicle,B:[int]vehicle,C:counter)<suspends>:void=
    defer:Print("cleanup {C.N}")
    F:=Concatenate(Take(A,C,1))
    Sleep(0.1)
    M:=ConcatenateMaps(Take(B,C,2),Take(B,C,3))
    if(X:=F[0],Y:=M[1]):
        set X.N+=10
        set Y.N+=100
        Print("step {X.N} {Y.N} {C.N}")
Launch(A:[][]vehicle,B:[int]vehicle,C:counter):task(void)=spawn{Wait(A,B,C)}
Main()<suspends>:void=
    P:=car{}
    Q:=car{N:=3}
    A:=array{P}
    B:=array{Q}
    C:=counter{}
    F:=Flatten(array{A,B},C)
    if(X:=F[0]):set X.N+=1
    Print("flatten {F.Length} {P.N} {C.N}")
    R:=Arrays(A,B,C)
    Print("arrays {R.Length} {C.N}")
    if(Arrays(A,B,C),false?)then Print("bad")else Print("rollback {P.N} {C.N}")
    set C.N=0
    M:=Maps(map{1=>P,2=>Q},map{2=>P,3=>Q},C)
    if(X:=M[2]):Print("maps {M.Length} {X.N} {C.N}")
    set P.N=7
    if(X:=F[0],Y:=R[0],Z:=M[2]):Print("aliases {X.N} {Y.N} {Z.N} {P.Name}")
    if(Attempt(array{A,B},C)?)then Print("bad")else Print("failed source {C.N}")
    W:=counter{}
    T:=Launch(array{A,B},map{1=>Q},W)
    Sleep(0.2)
    T.Await()
    Print("task {P.N} {Q.N} {W.N}")
    race:
        Wait(array{A,B},map{1=>Q},W)
        block:
            Sleep(0.05)
            Print("winner")
    Print("cancel {P.N} {Q.N} {W.N}")
