cell:=class{var N:int=0}
Values(H:cell)<transacts>:int=
    set H.N+=1
    3|4
Upper(H:cell,OK:logic)<transacts><decides>:int=
    set H.N+=10
    OK?
    1|2
Main()<transacts>:void=
    A:=cell{}
    for(I:=Values(A),I<0):Err()
    Print("producer {A.N}")
    B:=cell{}
    for(I:=block{set B.N+=1;3|4},I<0):Err()
    Print("literal {B.N}")
    C:=cell{}
    for(I:=Values(C),I=4):Print("accepted {I} {C.N}")
    Print("state {C.N}")
    D:=cell{}
    for(I:=Values(D)..Upper[D,false]):Err()
    Print("failed bounds {D.N}")
    E:=cell{}
    for(I:=Values(E)..Upper[E,true]):Err()
    Print("empty ranges {E.N}")
