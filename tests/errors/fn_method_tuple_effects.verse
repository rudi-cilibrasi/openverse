# expect: generic method of
box:=class:
    var N:int=0
    Pair(X:u,Y:u where u:type):tuple(u,u)=
        set N+=1
        (X,Y)
Main():void=
    F:type{_(:tuple(int,int))<computes>:tuple(int,int)}=box{}.Pair
