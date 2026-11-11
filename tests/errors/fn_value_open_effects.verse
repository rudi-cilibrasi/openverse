# expect: 'Read' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Read(X:t where t:type)<reads>:t=X
Use(X:t where t:type):void=
    F:type{_(:t)<computes>:t}=Read
Main():void=Use(3)
