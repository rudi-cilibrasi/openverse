# expect: a function type determining all its type arguments and satisfying its bounds must be expected
Pair(X:t,Y:u where t:type,u:type)<reads>:tuple(t,u)=(X,Y)
Run(X:a,Y:b where a:type,b:type):void=
    F:type{_(:tuple(a,b))<computes>:tuple(a,b)}=Pair
Main():void=Run(3,"s")
