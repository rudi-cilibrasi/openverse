# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box(t:type):=class:
    V:t
    Pair(X:u where u:type):tuple(t,u)=(V,X)
Main():void=
    F:type{_(:int):tuple(string,int)}=box(int){V:=3}.Pair
    Print("wrong")
