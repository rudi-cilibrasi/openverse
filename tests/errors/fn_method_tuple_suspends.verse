# expect: generic method of
box:=class:
    Later(P:tuple(u,u) where u:type)<suspends>:u=
        Sleep(0.0)
        P(0)
Main():void=
    F:type{_(:int,:int):int}=box{}.Later
