# expect: 'Fail' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Fail(X:t where t:type)<decides>:t=
    false?
    X
Use(X:t where t:type):void=
    F:type{_(:t):t}=Fail
Main():void=Use(3)
