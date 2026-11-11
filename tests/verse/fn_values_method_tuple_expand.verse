base(t:type):=class:
    V:t
    Flip(P:tuple(t,u,t) where u:type):tuple(t,u,t)=(P(2),P(1),P(0))
child(a:type):=class(base(a)):
    Flip<override>(P:tuple(a,b,a) where b:type):tuple(a,b,a)=(P(2),P(1),P(0))
Bind(B:base(t),X:u where t:type,u:type):type{_(:t,:u,:t):tuple(t,u,t)}=B.Flip
Main():void=
    F:=Bind(child(int){V:=7},"tag")
    R:=F(1,"x",3)
    Print("{R(0)} {R(1)} {R(2)}")
