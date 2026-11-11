# expect: 'Forget' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Forget(X:a where a:type,b:type):a=X
Use(X:t where t:type):void=
    F:type{_(:t):t}=Forget
Main():void=Use(3)
