# expect: generic method of
box:=class:
    Match(P:tuple(u,u) where u:subtype(comparable))<decides>:u=
        P(0)=P(1)
        P(0)
Main():void=
    F:type{_(:int,:int):int}=box{}.Match
