# expect: a function type determining all its type arguments and satisfying its bounds must be expected
Pair(X:t,Y:u where t:type,u:type)<suspends>:tuple(t,u)=block{Sleep(0.0);(X,Y)}
Run(X:a,Y:b where a:type,b:type):void=
    F:type{_(:tuple(a,b)):tuple(a,b)}=Pair
Main():void=Run(3,"s")
