cell:=class{var N:int=0}
Match(P:tuple(cell,t,t) where t:subtype(comparable))<transacts><decides>:t=
    C:=P(0)
    set C.N+=1
    Print("try {C.N}")
    P(1)=P(2)
    P(1)
Run(C:cell,X:t,Y:t where t:subtype(comparable))<transacts>:void=
    F:type{_(:cell,:t,:t)<transacts><decides>:t}=Match
    if(F[C,Y,X])then Print("wrong")else Print("miss {C.N}")
    if(F[C,X,X],Print("suffix"),false?)then Print("wrong")else Print("reject {C.N}")
    if(F[C,X,X])then Print("hit {C.N}")
Main():void=Run(cell{},3,4)
