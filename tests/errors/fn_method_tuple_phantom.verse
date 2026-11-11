# expect: generic method of
box:=class:
    Empty(X:int,Y:int where u:type):int=X+Y
Main():void=
    F:type{_(:tuple(int,int)):int}=box{}.Empty
