# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box:=class:
    Same(X:t where t:type)<reads>:t=X
Run(X:u where u:type):void=
    F:type{_(:u)<computes>:u}=box{}.Same
Main():void=Run(3)
