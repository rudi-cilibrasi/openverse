cell:=class{var N:int=0}
box(t:type,h:type):=class:
    V:t
    Hidden:h
    Empty(P:tuple()):t=V
    Get():t=V
    Id(X:u where u:type):u=X
Run(B:box(t,h),X:u where t:type,h:type,u:type):tuple(t,t,u,u)=
    F:type{_():t}=B.Empty
    G:type{_(:tuple()):t}=B.Get
    H:type{_(:tuple(u)):u}=B.Id
    I:type{_(:u):tuple(u)}=B.Id
    (F(),G(()),H(I(X)),I(X)(0))
Main():void=
    R:=Run(box(int,string){V:=1,Hidden:="hidden"},"input")
    Print("result {R(0)} {R(1)} {R(2)} {R(3)}")
