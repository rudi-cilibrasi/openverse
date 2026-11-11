# expect: 'Later' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Later(X:t where t:type)<suspends>:t=
    Sleep(0.0)
    X
Use(X:t where t:type):void=
    F:type{_(:t):t}=Later
Main():void=Use(3)
