# Covariant multi-value calls preserve static results and consumer boundaries (#283).
animal := class { N:int=0 }
dog := class(animal) { Bark:int=0 }
meter := class { var N:int=0 }
Note(S:string,V:int)<transacts>:int =
    Print(S)
    V
shelter := class:
    H:meter
    Get(N:int,?Q:int=Note("rootdefault",3))<transacts>:animal = animal{N:=N} | animal{N:=N+1}
kennel := class(shelter):
    Get<override>(N:int,?Q:int=Note("default",3))<transacts>:dog =
        Print("impl")
        dog{N:=N,Bark:=N+Q} | dog{N:=N+1,Bark:=N+Q+1}
single := class(kennel):
    Get<override>(N:int,?Q:int=Note("singledefault",3))<transacts>:dog =
        Print("single")
        dog{N:=N,Bark:=N+Q}
Recv(H:meter,K:kennel)<transacts>:kennel =
    set H.N += 1
    Print("recv {H.N}")
    K
Arg(H:meter)<transacts>:int =
    set H.N += 1
    Print("arg {H.N}")
    H.N
Main()<transacts>:void =
    H:=meter{}
    K:=kennel{H:=H}
    for(D:=Recv(H,K).Get(Arg(H)),D.Bark>5){Print("d {D.Bark}")}
    if(D:=Recv(H,K).Get(Arg(H)),D.Bark>10) then Print("bad") else Print("none {H.N}")
    for(D:=Recv(H,single{H:=H}).Get(Arg(H)),D.Bark>100){Print("bad")}
    Print("end {H.N}")
