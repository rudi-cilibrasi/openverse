# expect: found type{_(:tuple(int, string)):tuple(int, string)}
box(t:type):=class:
    Echo(X:t):t=X
Main():void=
    F:type{_(:int,:int):tuple(int,int)}=box(tuple(int,string)){}.Echo
