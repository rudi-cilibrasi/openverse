# expect: generic method of
box:=class:
    Id(X:u where u:subtype(comparable)):u=X
Bind(X:t where t:type):type{_(:t,:t):tuple(t,t)}=box{}.Id
Main():void={}
