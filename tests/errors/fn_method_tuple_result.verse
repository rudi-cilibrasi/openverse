# expect: generic method of
box:=class:
    Swap(P:tuple(a,b) where a:type,b:type):tuple(b,a)=(P(1),P(0))
Main():void=
    F:type{_(:int,:string):tuple(int,string)}=box{}.Swap
