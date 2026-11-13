vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Take(A:t,C:counter where t:subtype([]vehicle))<transacts>:t=
    set C.N+=1
    A
Walk(A:t,C:counter where t:subtype([]vehicle))<transacts>:int=
    var Sum:int=0
    for(X:Take(A,C)):
        set X.N+=1
        set Sum+=X.N
    Sum
Fail(A:t,C:counter where t:subtype([]vehicle))<transacts><decides>:t=
    set C.N+=1
    false?
    A
Skip(A:t,C:counter where t:subtype([]vehicle))<transacts>:[]int=for(X:Fail[A,C]):1
Select(A:t,C:counter where t:subtype([]int))<transacts>:[]int=for(V:A,(set C.N+=1;V>1)):V
Wait(A:t,C:counter where t:subtype([]vehicle))<suspends>:void=
    defer:Print("cleanup {C.N}")
    for(X:Take(A,C)):
        Sleep(0.1)
        set X.N+=10
        Print("step {X.N}")
Main()<suspends>:void=
    P:=car{Name:="a"}
    Q:=car{Name:="b",N:=3}
    A:=array{P,Q}
    C:=counter{}
    Print("walk {Walk(A,C)} {P.N} {Q.N} {C.N}")
    if(Walk(A,C),false?)then Print("bad")else Print("rollback {P.N} {Q.N} {C.N}")
    Print("failed source {Skip(A,C).Length} {C.N}")
    F:=counter{}
    R:=Select(array{1,2,3},F)
    Print("filter {R.Length} {F.N}")
    race:
        Wait(A,C)
        block:
            Sleep(0.15)
            Print("winner")
    Print("cancel {P.N} {Q.N} {C.N} {P.Name} {Q.Name}")
