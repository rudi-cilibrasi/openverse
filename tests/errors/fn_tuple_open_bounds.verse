# expect: a function type determining all its type arguments and satisfying its bounds must be expected
Id(X:t where t:subtype(comparable)):t=X
Run(X:a,Y:b where a:subtype(comparable),b:type):void=
    F:type{_(:a,:b):tuple(a,b)}=Id
Main():void=Run(3,"s")
