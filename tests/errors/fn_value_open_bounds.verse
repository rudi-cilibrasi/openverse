# expect: 'Same' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Same(X:t,Y:t where t:subtype(comparable))<decides>:t=
    X=Y
    X
Use(X:t where t:type):void=
    F:type{_(:t,:t)<decides>:t}=Same
Main():void=Use(1)
