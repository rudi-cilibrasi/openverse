cell:=class{var N:int=0}
Packet(C:cell,X:t,Y:u,Z:t where t:type,u:type):tuple(cell,t,u,t)=
    set C.N+=1
    Print("packet {C.N}")
    (C,X,Y,Z)
Many(C:cell,X:t,Y:u,Z:t where t:type,u:type):tuple(t,u,t)=
    set C.N+=1
    Print("many {C.N}")
    (X,Y,Z)
One(P:tuple(cell,t,u,t) where t:type,u:type):tuple(t,u,t)=
    C:=P(0)
    set C.N+=1
    Print("one {C.N}")
    (P(1),P(2),P(3))
Touch(C:cell):cell=
    set C.N+=1
    Print("argument {C.N}")
    C
Run(C:cell,X:t,Y:u,Z:t where t:type,u:type):tuple(t,u,t)=
    F:type{_(:tuple(cell,t,u,t)):tuple(t,u,t)}=Many
    G:type{_(:cell,:t,:u,:t):tuple(t,u,t)}=One
    A:=F(Packet(C,X,Y,Z))
    G(Touch(C),A(0),A(1),A(2))
Main():void=
    C:=cell{}
    R:=Run(C,7,"s",9)
    Print("result {R(0)} {R(1)} {R(2)} state {C.N}")
