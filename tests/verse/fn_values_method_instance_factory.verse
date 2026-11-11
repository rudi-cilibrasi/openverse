cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Echo(X:u where u:type):u=
        set C.N+=1
        Print("echo {C.N}")
        X
    Bind(X:u where u:type):type{_(:u):u}=Echo
    Default(X:u,?F:type{_(:u):u}=Echo where u:type):u=F(X)
Use(B:box(u),X:v where u:type,v:type):v=
    Factory:type{_(:v):type{_(:v):v}}=B.Bind
    F:=Factory(X)
    F(B.Default(X))
Main():void=Print("value {Use(box(string){V:="s",C:=cell{}},7)}")
