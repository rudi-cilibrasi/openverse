# expect: generic method of
box(t:type):=class:
    V:t
    Pair(X:u,Y:u where u:type):tuple(t,u,u)=(V,X,Y)
Main():void=
    F:type{_(:tuple(int,int)):tuple(int,int,int)}=box(string){V:="s"}.Pair
