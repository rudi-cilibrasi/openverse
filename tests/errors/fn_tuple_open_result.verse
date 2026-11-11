# expect: a function type determining all its type arguments and satisfying its bounds must be expected
Flip(P:tuple(t,u) where t:type,u:type):tuple(u,t)=(P(1),P(0))
Run(X:a,Y:b where a:type,b:type):void=
    F:type{_(:a,:b):tuple(a,b)}=Flip
Main():void=Run(3,"s")
