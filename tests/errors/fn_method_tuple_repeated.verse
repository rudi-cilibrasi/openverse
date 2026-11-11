# expect: generic method of
box:=class:
    Pair(X:u,Y:u where u:type):tuple(u,u)=(X,Y)
Main():void=
    F:type{_(:tuple(int,string)):tuple(int,string)}=box{}.Pair
