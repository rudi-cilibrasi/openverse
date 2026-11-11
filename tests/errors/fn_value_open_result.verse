# expect: 'Id' is generic: a function type determining all its type arguments and satisfying its bounds must be expected
Id(X:t where t:type):t=X
Use(X:a,Y:b where a:type,b:type):void=
    F:type{_(:a):b}=Id
Main():void=Use(1,"s")
